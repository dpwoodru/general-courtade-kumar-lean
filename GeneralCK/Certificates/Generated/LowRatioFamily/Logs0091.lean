import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5824_neg : (191881 / 1000000000) ≤ -Real.log (10000000 / 10001919) ∧
    -Real.log (10000000 / 10001919) ≤ (95941 / 500000000) := by
  have h := checkLog_sound (w := (1919 / 20001919)) (n := 12)
    (lo := (191881 / 1000000000)) (hi := (95941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001919 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001919 / 10000000) = 1/(10000000 / 10001919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5824 : Bounds (191881 / 1000000000) (95941 / 500000000) (Real.log (10001919 / 10000000)) := by
  have h := reflection_log_5824_neg
  have he : Real.log (10001919 / 10000000) = -Real.log (10000000 / 10001919) := by
    rw [show ((10001919 / 10000000) : ℝ) = ((10000000 / 10001919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5825_neg : (95959 / 500000000) ≤ -Real.log (9998081 / 10000000) ∧
    -Real.log (9998081 / 10000000) ≤ (191919 / 1000000000) := by
  have h := checkLog_sound (w := (1919 / 19998081)) (n := 12)
    (lo := (95959 / 500000000)) (hi := (191919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998081) = 1/(9998081 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5825 : Bounds (-191919 / 1000000000) (-95959 / 500000000) (Real.log (9998081 / 10000000)) := by
  have h := reflection_log_5825_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5826_neg : (11509369 / 125000000) ≤ -Real.log (1000000 / 1096447) ∧
    -Real.log (1000000 / 1096447) ≤ (92074953 / 1000000000) := by
  have h := checkLog_sound (w := (96447 / 2096447)) (n := 12)
    (lo := (11509369 / 125000000)) (hi := (92074953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096447 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096447 / 1000000) = 1/(1000000 / 1096447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5826 : Bounds (11509369 / 125000000) (92074953 / 1000000000) (Real.log (1096447 / 1000000)) := by
  have h := reflection_log_5826_neg
  have he : Real.log (1096447 / 1000000) = -Real.log (1000000 / 1096447) := by
    rw [show ((1096447 / 1000000) : ℝ) = ((1000000 / 1096447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5827_neg : (101420509 / 1000000000) ≤ -Real.log (903553 / 1000000) ∧
    -Real.log (903553 / 1000000) ≤ (10142051 / 100000000) := by
  have h := checkLog_sound (w := (96447 / 1903553)) (n := 12)
    (lo := (101420509 / 1000000000)) (hi := (10142051 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903553) = 1/(903553 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5827 : Bounds (-10142051 / 100000000) (-101420509 / 1000000000) (Real.log (903553 / 1000000)) := by
  have h := reflection_log_5827_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5828_neg : (11537069 / 125000000) ≤ -Real.log (100000 / 109669) ∧
    -Real.log (100000 / 109669) ≤ (92296553 / 1000000000) := by
  have h := checkLog_sound (w := (9669 / 209669)) (n := 12)
    (lo := (11537069 / 125000000)) (hi := (92296553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109669 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109669 / 100000) = 1/(100000 / 109669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5828 : Bounds (11537069 / 125000000) (92296553 / 1000000000) (Real.log (109669 / 100000)) := by
  have h := reflection_log_5828_neg
  have he : Real.log (109669 / 100000) = -Real.log (100000 / 109669) := by
    rw [show ((109669 / 100000) : ℝ) = ((100000 / 109669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5829_neg : (25422371 / 250000000) ≤ -Real.log (90331 / 100000) ∧
    -Real.log (90331 / 100000) ≤ (20337897 / 200000000) := by
  have h := checkLog_sound (w := (9669 / 190331)) (n := 12)
    (lo := (25422371 / 250000000)) (hi := (20337897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90331) = 1/(90331 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5829 : Bounds (-20337897 / 200000000) (-25422371 / 250000000) (Real.log (90331 / 100000)) := by
  have h := reflection_log_5829_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5830_neg : (9392931 / 1000000000) ≤ -Real.log (9906510439 / 10000000000) ∧
    -Real.log (9906510439 / 10000000000) ≤ (2348233 / 250000000) := by
  have h := checkLog_sound (w := (93489561 / 19906510439)) (n := 12)
    (lo := (9392931 / 1000000000)) (hi := (2348233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9906510439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9906510439) = 1/(9906510439 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5830 : Bounds (-2348233 / 250000000) (-9392931 / 1000000000) (Real.log (9906510439 / 10000000000)) := by
  have h := reflection_log_5830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5831_neg : (9345557 / 1000000000) ≤ -Real.log (990697976191 / 1000000000000) ∧
    -Real.log (990697976191 / 1000000000000) ≤ (4672779 / 500000000) := by
  have h := checkLog_sound (w := (9302023809 / 1990697976191)) (n := 12)
    (lo := (9345557 / 1000000000)) (hi := (4672779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990697976191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990697976191) = 1/(990697976191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5831 : Bounds (-4672779 / 500000000) (-9345557 / 1000000000) (Real.log (990697976191 / 1000000000000)) := by
  have h := reflection_log_5831_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5832_neg : (96747731 / 500000000) ≤ -Real.log (4000000000 / 4853935519) ∧
    -Real.log (4000000000 / 4853935519) ≤ (193495463 / 1000000000) := by
  have h := checkLog_sound (w := (853935519 / 8853935519)) (n := 12)
    (lo := (96747731 / 500000000)) (hi := (193495463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4853935519 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4853935519 / 4000000000) = 1/(4000000000 / 4853935519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5832 : Bounds (96747731 / 500000000) (193495463 / 1000000000) (Real.log (4853935519 / 4000000000)) := by
  have h := reflection_log_5832_neg
  have he : Real.log (4853935519 / 4000000000) = -Real.log (4000000000 / 4853935519) := by
    rw [show ((4853935519 / 4000000000) : ℝ) = ((4000000000 / 4853935519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5833_neg : (48496509 / 250000000) ≤ -Real.log (31250000000 / 37939979077) ∧
    -Real.log (31250000000 / 37939979077) ≤ (193986037 / 1000000000) := by
  have h := checkLog_sound (w := (6689979077 / 69189979077)) (n := 12)
    (lo := (48496509 / 250000000)) (hi := (193986037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37939979077 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37939979077 / 31250000000) = 1/(31250000000 / 37939979077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5833 : Bounds (48496509 / 250000000) (193986037 / 1000000000) (Real.log (37939979077 / 31250000000)) := by
  have h := reflection_log_5833_neg
  have he : Real.log (37939979077 / 31250000000) = -Real.log (31250000000 / 37939979077) := by
    rw [show ((37939979077 / 31250000000) : ℝ) = ((31250000000 / 37939979077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5834_neg : (77682099 / 200000000) ≤ -Real.log (500000000000 / 737317495669) ∧
    -Real.log (500000000000 / 737317495669) ≤ (3034457 / 7812500) := by
  have h := checkLog_sound (w := (237317495669 / 1237317495669)) (n := 12)
    (lo := (77682099 / 200000000)) (hi := (3034457 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737317495669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737317495669 / 500000000000) = 1/(500000000000 / 737317495669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5834 : Bounds (77682099 / 200000000) (3034457 / 7812500) (Real.log (737317495669 / 500000000000)) := by
  have h := reflection_log_5834_neg
  have he : Real.log (737317495669 / 500000000000) = -Real.log (500000000000 / 737317495669) := by
    rw [show ((737317495669 / 500000000000) : ℝ) = ((500000000000 / 737317495669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5835_neg : (194309069 / 500000000) ≤ -Real.log (250000000000 / 368735305037) ∧
    -Real.log (250000000000 / 368735305037) ≤ (388618139 / 1000000000) := by
  have h := checkLog_sound (w := (118735305037 / 618735305037)) (n := 12)
    (lo := (194309069 / 500000000)) (hi := (388618139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368735305037 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(368735305037 / 250000000000) = 1/(250000000000 / 368735305037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5835 : Bounds (194309069 / 500000000) (388618139 / 1000000000) (Real.log (368735305037 / 250000000000)) := by
  have h := reflection_log_5835_neg
  have he : Real.log (368735305037 / 250000000000) = -Real.log (250000000000 / 368735305037) := by
    rw [show ((368735305037 / 250000000000) : ℝ) = ((250000000000 / 368735305037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5836_neg : (21954071 / 125000000) ≤ -Real.log (125 / 149) ∧
    -Real.log (125 / 149) ≤ (175632569 / 1000000000) := by
  have h := checkLog_sound (w := (12 / 137)) (n := 12)
    (lo := (21954071 / 125000000)) (hi := (175632569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149 / 125) = 1/(125 / 149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5836 : Bounds (21954071 / 125000000) (175632569 / 1000000000) (Real.log (149 / 125)) := by
  have h := reflection_log_5836_neg
  have he : Real.log (149 / 125) = -Real.log (125 / 149) := by
    rw [show ((149 / 125) : ℝ) = ((125 / 149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5837_neg : (10659661 / 50000000) ≤ -Real.log (101 / 125) ∧
    -Real.log (101 / 125) ≤ (213193221 / 1000000000) := by
  have h := checkLog_sound (w := (12 / 113)) (n := 12)
    (lo := (10659661 / 50000000)) (hi := (213193221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 101) = 1/(101 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5837 : Bounds (-213193221 / 1000000000) (-10659661 / 50000000) (Real.log (101 / 125)) := by
  have h := reflection_log_5837_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5838_neg : (191981 / 1000000000) ≤ -Real.log (15625 / 15628) ∧
    -Real.log (15625 / 15628) ≤ (95991 / 500000000) := by
  have h := checkLog_sound (w := (3 / 31253)) (n := 12)
    (lo := (191981 / 1000000000)) (hi := (95991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15628 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15628 / 15625) = 1/(15625 / 15628) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5838 : Bounds (191981 / 1000000000) (95991 / 500000000) (Real.log (15628 / 15625)) := by
  have h := reflection_log_5838_neg
  have he : Real.log (15628 / 15625) = -Real.log (15625 / 15628) := by
    rw [show ((15628 / 15625) : ℝ) = ((15625 / 15628) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5839_neg : (96009 / 500000000) ≤ -Real.log (15622 / 15625) ∧
    -Real.log (15622 / 15625) ≤ (192019 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 31247)) (n := 12)
    (lo := (96009 / 500000000)) (hi := (192019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15622) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 15622) = 1/(15622 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5839 : Bounds (-192019 / 1000000000) (-96009 / 500000000) (Real.log (15622 / 15625)) := by
  have h := reflection_log_5839_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5840_neg : (11515183 / 125000000) ≤ -Real.log (500000 / 548249) ∧
    -Real.log (500000 / 548249) ≤ (18424293 / 200000000) := by
  have h := checkLog_sound (w := (48249 / 1048249)) (n := 12)
    (lo := (11515183 / 125000000)) (hi := (18424293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548249 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548249 / 500000) = 1/(500000 / 548249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5840 : Bounds (11515183 / 125000000) (18424293 / 200000000) (Real.log (548249 / 500000)) := by
  have h := reflection_log_5840_neg
  have he : Real.log (548249 / 500000) = -Real.log (500000 / 548249) := by
    rw [show ((548249 / 500000) : ℝ) = ((500000 / 548249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5841_neg : (20295391 / 200000000) ≤ -Real.log (451751 / 500000) ∧
    -Real.log (451751 / 500000) ≤ (25369239 / 250000000) := by
  have h := checkLog_sound (w := (48249 / 951751)) (n := 12)
    (lo := (20295391 / 200000000)) (hi := (25369239 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451751) = 1/(451751 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5841 : Bounds (-25369239 / 250000000) (-20295391 / 200000000) (Real.log (451751 / 500000)) := by
  have h := reflection_log_5841_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5842_neg : (46171527 / 500000000) ≤ -Real.log (1000000 / 1096741) ∧
    -Real.log (1000000 / 1096741) ≤ (18468611 / 200000000) := by
  have h := checkLog_sound (w := (96741 / 2096741)) (n := 12)
    (lo := (46171527 / 500000000)) (hi := (18468611 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096741 / 1000000) = 1/(1000000 / 1096741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5842 : Bounds (46171527 / 500000000) (18468611 / 200000000) (Real.log (1096741 / 1000000)) := by
  have h := reflection_log_5842_neg
  have he : Real.log (1096741 / 1000000) = -Real.log (1000000 / 1096741) := by
    rw [show ((1096741 / 1000000) : ℝ) = ((1000000 / 1096741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5843_neg : (12718243 / 125000000) ≤ -Real.log (903259 / 1000000) ∧
    -Real.log (903259 / 1000000) ≤ (20349189 / 200000000) := by
  have h := checkLog_sound (w := (96741 / 1903259)) (n := 12)
    (lo := (12718243 / 125000000)) (hi := (20349189 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903259) = 1/(903259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5843 : Bounds (-20349189 / 200000000) (-12718243 / 125000000) (Real.log (903259 / 1000000)) := by
  have h := reflection_log_5843_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5844_neg : (940289 / 100000000) ≤ -Real.log (990641178919 / 1000000000000) ∧
    -Real.log (990641178919 / 1000000000000) ≤ (9402891 / 1000000000) := by
  have h := checkLog_sound (w := (9358821081 / 1990641178919)) (n := 12)
    (lo := (940289 / 100000000)) (hi := (9402891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990641178919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990641178919) = 1/(990641178919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5844 : Bounds (-9402891 / 1000000000) (-940289 / 100000000) (Real.log (990641178919 / 1000000000000)) := by
  have h := reflection_log_5844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5845_neg : (935549 / 100000000) ≤ -Real.log (247672033999 / 250000000000) ∧
    -Real.log (247672033999 / 250000000000) ≤ (9355491 / 1000000000) := by
  have h := checkLog_sound (w := (2327966001 / 497672033999)) (n := 12)
    (lo := (935549 / 100000000)) (hi := (9355491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247672033999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247672033999) = 1/(247672033999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5845 : Bounds (-9355491 / 1000000000) (-935549 / 100000000) (Real.log (247672033999 / 250000000000)) := by
  have h := reflection_log_5845_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5846_neg : (9679921 / 50000000) ≤ -Real.log (100000000000 / 121360882433) ∧
    -Real.log (100000000000 / 121360882433) ≤ (193598421 / 1000000000) := by
  have h := checkLog_sound (w := (21360882433 / 221360882433)) (n := 12)
    (lo := (9679921 / 50000000)) (hi := (193598421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121360882433 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121360882433 / 100000000000) = 1/(100000000000 / 121360882433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5846 : Bounds (9679921 / 50000000) (193598421 / 1000000000) (Real.log (121360882433 / 100000000000)) := by
  have h := reflection_log_5846_neg
  have he : Real.log (121360882433 / 100000000000) = -Real.log (100000000000 / 121360882433) := by
    rw [show ((121360882433 / 100000000000) : ℝ) = ((100000000000 / 121360882433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5847_neg : (194088999 / 1000000000) ≤ -Real.log (500000000000 / 607102171139) ∧
    -Real.log (500000000000 / 607102171139) ≤ (194089 / 1000000) := by
  have h := checkLog_sound (w := (107102171139 / 1107102171139)) (n := 12)
    (lo := (194088999 / 1000000000)) (hi := (194089 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607102171139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607102171139 / 500000000000) = 1/(500000000000 / 607102171139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5847 : Bounds (194088999 / 1000000000) (194089 / 1000000) (Real.log (607102171139 / 500000000000)) := by
  have h := reflection_log_5847_neg
  have he : Real.log (607102171139 / 500000000000) = -Real.log (500000000000 / 607102171139) := by
    rw [show ((607102171139 / 500000000000) : ℝ) = ((500000000000 / 607102171139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5848_neg : (194309069 / 500000000) ≤ -Real.log (500000000000 / 737470610073) ∧
    -Real.log (500000000000 / 737470610073) ≤ (388618139 / 1000000000) := by
  have h := checkLog_sound (w := (237470610073 / 1237470610073)) (n := 12)
    (lo := (194309069 / 500000000)) (hi := (388618139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737470610073 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737470610073 / 500000000000) = 1/(500000000000 / 737470610073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5848 : Bounds (194309069 / 500000000) (388618139 / 1000000000) (Real.log (737470610073 / 500000000000)) := by
  have h := reflection_log_5848_neg
  have he : Real.log (737470610073 / 500000000000) = -Real.log (500000000000 / 737470610073) := by
    rw [show ((737470610073 / 500000000000) : ℝ) = ((500000000000 / 737470610073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5849_neg : (388825789 / 1000000000) ≤ -Real.log (500000000000 / 737623762377) ∧
    -Real.log (500000000000 / 737623762377) ≤ (38882579 / 100000000) := by
  have h := checkLog_sound (w := (237623762377 / 1237623762377)) (n := 12)
    (lo := (388825789 / 1000000000)) (hi := (38882579 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737623762377 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737623762377 / 500000000000) = 1/(500000000000 / 737623762377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5849 : Bounds (388825789 / 1000000000) (38882579 / 100000000) (Real.log (737623762377 / 500000000000)) := by
  have h := reflection_log_5849_neg
  have he : Real.log (737623762377 / 500000000000) = -Real.log (500000000000 / 737623762377) := by
    rw [show ((737623762377 / 500000000000) : ℝ) = ((500000000000 / 737623762377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5850_neg : (175716457 / 1000000000) ≤ -Real.log (10000 / 11921) ∧
    -Real.log (10000 / 11921) ≤ (87858229 / 500000000) := by
  have h := checkLog_sound (w := (1921 / 21921)) (n := 12)
    (lo := (175716457 / 1000000000)) (hi := (87858229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11921 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11921 / 10000) = 1/(10000 / 11921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5850 : Bounds (175716457 / 1000000000) (87858229 / 500000000) (Real.log (11921 / 10000)) := by
  have h := reflection_log_5850_neg
  have he : Real.log (11921 / 10000) = -Real.log (10000 / 11921) := by
    rw [show ((11921 / 10000) : ℝ) = ((10000 / 11921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5851_neg : (21331699 / 100000000) ≤ -Real.log (8079 / 10000) ∧
    -Real.log (8079 / 10000) ≤ (213316991 / 1000000000) := by
  have h := checkLog_sound (w := (1921 / 18079)) (n := 12)
    (lo := (21331699 / 100000000)) (hi := (213316991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8079) = 1/(8079 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5851 : Bounds (-213316991 / 1000000000) (-21331699 / 100000000) (Real.log (8079 / 10000)) := by
  have h := reflection_log_5851_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5852_neg : (192081 / 1000000000) ≤ -Real.log (10000000 / 10001921) ∧
    -Real.log (10000000 / 10001921) ≤ (96041 / 500000000) := by
  have h := checkLog_sound (w := (1921 / 20001921)) (n := 12)
    (lo := (192081 / 1000000000)) (hi := (96041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001921 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001921 / 10000000) = 1/(10000000 / 10001921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5852 : Bounds (192081 / 1000000000) (96041 / 500000000) (Real.log (10001921 / 10000000)) := by
  have h := reflection_log_5852_neg
  have he : Real.log (10001921 / 10000000) = -Real.log (10000000 / 10001921) := by
    rw [show ((10001921 / 10000000) : ℝ) = ((10000000 / 10001921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5853_neg : (96059 / 500000000) ≤ -Real.log (9998079 / 10000000) ∧
    -Real.log (9998079 / 10000000) ≤ (192119 / 1000000000) := by
  have h := checkLog_sound (w := (1921 / 19998079)) (n := 12)
    (lo := (96059 / 500000000)) (hi := (192119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998079) = 1/(9998079 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5853 : Bounds (-192119 / 1000000000) (-96059 / 500000000) (Real.log (9998079 / 10000000)) := by
  have h := reflection_log_5853_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5854_neg : (3686719 / 40000000) ≤ -Real.log (1000000 / 1096549) ∧
    -Real.log (1000000 / 1096549) ≤ (11520997 / 125000000) := by
  have h := checkLog_sound (w := (96549 / 2096549)) (n := 12)
    (lo := (3686719 / 40000000)) (hi := (11520997 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096549 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096549 / 1000000) = 1/(1000000 / 1096549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5854 : Bounds (3686719 / 40000000) (11520997 / 125000000) (Real.log (1096549 / 1000000)) := by
  have h := reflection_log_5854_neg
  have he : Real.log (1096549 / 1000000) = -Real.log (1000000 / 1096549) := by
    rw [show ((1096549 / 1000000) : ℝ) = ((1000000 / 1096549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5855_neg : (101533403 / 1000000000) ≤ -Real.log (903451 / 1000000) ∧
    -Real.log (903451 / 1000000) ≤ (25383351 / 250000000) := by
  have h := checkLog_sound (w := (96549 / 1903451)) (n := 12)
    (lo := (101533403 / 1000000000)) (hi := (25383351 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903451) = 1/(903451 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5855 : Bounds (-25383351 / 250000000) (-101533403 / 1000000000) (Real.log (903451 / 1000000)) := by
  have h := reflection_log_5855_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5856_neg : (18477911 / 200000000) ≤ -Real.log (125000 / 137099) ∧
    -Real.log (125000 / 137099) ≤ (23097389 / 250000000) := by
  have h := checkLog_sound (w := (12099 / 262099)) (n := 12)
    (lo := (18477911 / 200000000)) (hi := (23097389 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137099 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137099 / 125000) = 1/(125000 / 137099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5856 : Bounds (18477911 / 200000000) (23097389 / 250000000) (Real.log (137099 / 125000)) := by
  have h := reflection_log_5856_neg
  have he : Real.log (137099 / 125000) = -Real.log (125000 / 137099) := by
    rw [show ((137099 / 125000) : ℝ) = ((125000 / 137099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5857_neg : (12725301 / 125000000) ≤ -Real.log (112901 / 125000) ∧
    -Real.log (112901 / 125000) ≤ (101802409 / 1000000000) := by
  have h := checkLog_sound (w := (12099 / 237901)) (n := 12)
    (lo := (12725301 / 125000000)) (hi := (101802409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112901) = 1/(112901 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5857 : Bounds (-101802409 / 1000000000) (-12725301 / 125000000) (Real.log (112901 / 125000)) := by
  have h := reflection_log_5857_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5858_neg : (9412853 / 1000000000) ≤ -Real.log (15478614199 / 15625000000) ∧
    -Real.log (15478614199 / 15625000000) ≤ (4706427 / 500000000) := by
  have h := checkLog_sound (w := (146385801 / 31103614199)) (n := 12)
    (lo := (9412853 / 1000000000)) (hi := (4706427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15478614199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15478614199) = 1/(15478614199 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5858 : Bounds (-4706427 / 500000000) (-9412853 / 1000000000) (Real.log (15478614199 / 15625000000)) := by
  have h := reflection_log_5858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5859_neg : (2341357 / 250000000) ≤ -Real.log (990678290599 / 1000000000000) ∧
    -Real.log (990678290599 / 1000000000000) ≤ (9365429 / 1000000000) := by
  have h := checkLog_sound (w := (9321709401 / 1990678290599)) (n := 12)
    (lo := (2341357 / 250000000)) (hi := (9365429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990678290599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990678290599) = 1/(990678290599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5859 : Bounds (-9365429 / 1000000000) (-2341357 / 250000000) (Real.log (990678290599 / 1000000000000)) := by
  have h := reflection_log_5859_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5860_neg : (193701379 / 1000000000) ≤ -Real.log (125000000000 / 151716722877) ∧
    -Real.log (125000000000 / 151716722877) ≤ (9685069 / 50000000) := by
  have h := checkLog_sound (w := (26716722877 / 276716722877)) (n := 12)
    (lo := (193701379 / 1000000000)) (hi := (9685069 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151716722877 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151716722877 / 125000000000) = 1/(125000000000 / 151716722877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5860 : Bounds (193701379 / 1000000000) (9685069 / 50000000) (Real.log (151716722877 / 125000000000)) := by
  have h := reflection_log_5860_neg
  have he : Real.log (151716722877 / 125000000000) = -Real.log (125000000000 / 151716722877) := by
    rw [show ((151716722877 / 125000000000) : ℝ) = ((125000000000 / 151716722877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5861_neg : (48547991 / 250000000) ≤ -Real.log (62500000000 / 75895585513) ∧
    -Real.log (62500000000 / 75895585513) ≤ (38838393 / 200000000) := by
  have h := checkLog_sound (w := (13395585513 / 138395585513)) (n := 12)
    (lo := (48547991 / 250000000)) (hi := (38838393 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75895585513 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75895585513 / 62500000000) = 1/(62500000000 / 75895585513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5861 : Bounds (48547991 / 250000000) (38838393 / 200000000) (Real.log (75895585513 / 62500000000)) := by
  have h := reflection_log_5861_neg
  have he : Real.log (75895585513 / 62500000000) = -Real.log (62500000000 / 75895585513) := by
    rw [show ((75895585513 / 62500000000) : ℝ) = ((62500000000 / 75895585513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5862_neg : (388825789 / 1000000000) ≤ -Real.log (62500000000 / 92202970297) ∧
    -Real.log (62500000000 / 92202970297) ≤ (38882579 / 100000000) := by
  have h := checkLog_sound (w := (29702970297 / 154702970297)) (n := 12)
    (lo := (388825789 / 1000000000)) (hi := (38882579 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92202970297 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92202970297 / 62500000000) = 1/(62500000000 / 92202970297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5862 : Bounds (388825789 / 1000000000) (38882579 / 100000000) (Real.log (92202970297 / 62500000000)) := by
  have h := reflection_log_5862_neg
  have he : Real.log (92202970297 / 62500000000) = -Real.log (62500000000 / 92202970297) := by
    rw [show ((92202970297 / 62500000000) : ℝ) = ((62500000000 / 92202970297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5863_neg : (48629181 / 125000000) ≤ -Real.log (250000000000 / 368888476297) ∧
    -Real.log (250000000000 / 368888476297) ≤ (389033449 / 1000000000) := by
  have h := checkLog_sound (w := (118888476297 / 618888476297)) (n := 12)
    (lo := (48629181 / 125000000)) (hi := (389033449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368888476297 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(368888476297 / 250000000000) = 1/(250000000000 / 368888476297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5863 : Bounds (48629181 / 125000000) (389033449 / 1000000000) (Real.log (368888476297 / 250000000000)) := by
  have h := reflection_log_5863_neg
  have he : Real.log (368888476297 / 250000000000) = -Real.log (250000000000 / 368888476297) := by
    rw [show ((368888476297 / 250000000000) : ℝ) = ((250000000000 / 368888476297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5864_neg : (175800339 / 1000000000) ≤ -Real.log (5000 / 5961) ∧
    -Real.log (5000 / 5961) ≤ (8790017 / 50000000) := by
  have h := checkLog_sound (w := (961 / 10961)) (n := 12)
    (lo := (175800339 / 1000000000)) (hi := (8790017 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5961 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5961 / 5000) = 1/(5000 / 5961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5864 : Bounds (175800339 / 1000000000) (8790017 / 50000000) (Real.log (5961 / 5000)) := by
  have h := reflection_log_5864_neg
  have he : Real.log (5961 / 5000) = -Real.log (5000 / 5961) := by
    rw [show ((5961 / 5000) : ℝ) = ((5000 / 5961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5865_neg : (8537631 / 40000000) ≤ -Real.log (4039 / 5000) ∧
    -Real.log (4039 / 5000) ≤ (26680097 / 125000000) := by
  have h := checkLog_sound (w := (961 / 9039)) (n := 12)
    (lo := (8537631 / 40000000)) (hi := (26680097 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4039) = 1/(4039 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5865 : Bounds (-26680097 / 125000000) (-8537631 / 40000000) (Real.log (4039 / 5000)) := by
  have h := reflection_log_5865_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5866_neg : (192181 / 1000000000) ≤ -Real.log (5000000 / 5000961) ∧
    -Real.log (5000000 / 5000961) ≤ (96091 / 500000000) := by
  have h := checkLog_sound (w := (961 / 10000961)) (n := 12)
    (lo := (192181 / 1000000000)) (hi := (96091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000961 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000961 / 5000000) = 1/(5000000 / 5000961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5866 : Bounds (192181 / 1000000000) (96091 / 500000000) (Real.log (5000961 / 5000000)) := by
  have h := reflection_log_5866_neg
  have he : Real.log (5000961 / 5000000) = -Real.log (5000000 / 5000961) := by
    rw [show ((5000961 / 5000000) : ℝ) = ((5000000 / 5000961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5867_neg : (96109 / 500000000) ≤ -Real.log (4999039 / 5000000) ∧
    -Real.log (4999039 / 5000000) ≤ (192219 / 1000000000) := by
  have h := checkLog_sound (w := (961 / 9999039)) (n := 12)
    (lo := (96109 / 500000000)) (hi := (192219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999039) = 1/(4999039 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5867 : Bounds (-192219 / 1000000000) (-96109 / 500000000) (Real.log (4999039 / 5000000)) := by
  have h := reflection_log_5867_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5868_neg : (92214483 / 1000000000) ≤ -Real.log (5000 / 5483) ∧
    -Real.log (5000 / 5483) ≤ (23053621 / 250000000) := by
  have h := checkLog_sound (w := (483 / 10483)) (n := 12)
    (lo := (92214483 / 1000000000)) (hi := (23053621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5483 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5483 / 5000) = 1/(5000 / 5483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5868 : Bounds (92214483 / 1000000000) (23053621 / 250000000) (Real.log (5483 / 5000)) := by
  have h := reflection_log_5868_neg
  have he : Real.log (5483 / 5000) = -Real.log (5000 / 5483) := by
    rw [show ((5483 / 5000) : ℝ) = ((5000 / 5483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5869_neg : (20317971 / 200000000) ≤ -Real.log (4517 / 5000) ∧
    -Real.log (4517 / 5000) ≤ (3174683 / 31250000) := by
  have h := checkLog_sound (w := (483 / 9517)) (n := 12)
    (lo := (20317971 / 200000000)) (hi := (3174683 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4517) = 1/(4517 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5869 : Bounds (-3174683 / 31250000) (-20317971 / 200000000) (Real.log (4517 / 5000)) := by
  have h := reflection_log_5869_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5870_neg : (92436053 / 1000000000) ≤ -Real.log (1000000 / 1096843) ∧
    -Real.log (1000000 / 1096843) ≤ (46218027 / 500000000) := by
  have h := checkLog_sound (w := (96843 / 2096843)) (n := 12)
    (lo := (92436053 / 1000000000)) (hi := (46218027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096843 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096843 / 1000000) = 1/(1000000 / 1096843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5870 : Bounds (92436053 / 1000000000) (46218027 / 500000000) (Real.log (1096843 / 1000000)) := by
  have h := reflection_log_5870_neg
  have he : Real.log (1096843 / 1000000) = -Real.log (1000000 / 1096843) := by
    rw [show ((1096843 / 1000000) : ℝ) = ((1000000 / 1096843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5871_neg : (814871 / 8000000) ≤ -Real.log (903157 / 1000000) ∧
    -Real.log (903157 / 1000000) ≤ (25464719 / 250000000) := by
  have h := checkLog_sound (w := (96843 / 1903157)) (n := 12)
    (lo := (814871 / 8000000)) (hi := (25464719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903157) = 1/(903157 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5871 : Bounds (-25464719 / 250000000) (-814871 / 8000000) (Real.log (903157 / 1000000)) := by
  have h := reflection_log_5871_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5872_neg : (4711411 / 500000000) ≤ -Real.log (990621433351 / 1000000000000) ∧
    -Real.log (990621433351 / 1000000000000) ≤ (9422823 / 1000000000) := by
  have h := checkLog_sound (w := (9378566649 / 1990621433351)) (n := 12)
    (lo := (4711411 / 500000000)) (hi := (9422823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990621433351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990621433351) = 1/(990621433351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5872 : Bounds (-9422823 / 1000000000) (-4711411 / 500000000) (Real.log (990621433351 / 1000000000000)) := by
  have h := reflection_log_5872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5873_neg : (9375371 / 1000000000) ≤ -Real.log (24766711 / 25000000) ∧
    -Real.log (24766711 / 25000000) ≤ (2343843 / 250000000) := by
  have h := checkLog_sound (w := (233289 / 49766711)) (n := 12)
    (lo := (9375371 / 1000000000)) (hi := (2343843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000000 / 24766711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000000 / 24766711) = 1/(24766711 / 25000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5873 : Bounds (-2343843 / 250000000) (-9375371 / 1000000000) (Real.log (24766711 / 25000000)) := by
  have h := reflection_log_5873_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5874_neg : (193804339 / 1000000000) ≤ -Real.log (100000000000 / 121385875581) ∧
    -Real.log (100000000000 / 121385875581) ≤ (9690217 / 50000000) := by
  have h := checkLog_sound (w := (21385875581 / 221385875581)) (n := 12)
    (lo := (193804339 / 1000000000)) (hi := (9690217 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121385875581 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121385875581 / 100000000000) = 1/(100000000000 / 121385875581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5874 : Bounds (193804339 / 1000000000) (9690217 / 50000000) (Real.log (121385875581 / 100000000000)) := by
  have h := reflection_log_5874_neg
  have he : Real.log (121385875581 / 100000000000) = -Real.log (100000000000 / 121385875581) := by
    rw [show ((121385875581 / 100000000000) : ℝ) = ((100000000000 / 121385875581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5875_neg : (194294929 / 1000000000) ≤ -Real.log (50000000000 / 60722720413) ∧
    -Real.log (50000000000 / 60722720413) ≤ (19429493 / 100000000) := by
  have h := checkLog_sound (w := (10722720413 / 110722720413)) (n := 12)
    (lo := (194294929 / 1000000000)) (hi := (19429493 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60722720413 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60722720413 / 50000000000) = 1/(50000000000 / 60722720413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5875 : Bounds (194294929 / 1000000000) (19429493 / 100000000) (Real.log (60722720413 / 50000000000)) := by
  have h := reflection_log_5875_neg
  have he : Real.log (60722720413 / 50000000000) = -Real.log (50000000000 / 60722720413) := by
    rw [show ((60722720413 / 50000000000) : ℝ) = ((50000000000 / 60722720413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5876_neg : (48629181 / 125000000) ≤ -Real.log (500000000000 / 737776952593) ∧
    -Real.log (500000000000 / 737776952593) ≤ (389033449 / 1000000000) := by
  have h := checkLog_sound (w := (237776952593 / 1237776952593)) (n := 12)
    (lo := (48629181 / 125000000)) (hi := (389033449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737776952593 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737776952593 / 500000000000) = 1/(500000000000 / 737776952593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5876 : Bounds (48629181 / 125000000) (389033449 / 1000000000) (Real.log (737776952593 / 500000000000)) := by
  have h := reflection_log_5876_neg
  have he : Real.log (737776952593 / 500000000000) = -Real.log (500000000000 / 737776952593) := by
    rw [show ((737776952593 / 500000000000) : ℝ) = ((500000000000 / 737776952593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5877_neg : (77848223 / 200000000) ≤ -Real.log (250000000000 / 368965090369) ∧
    -Real.log (250000000000 / 368965090369) ≤ (97310279 / 250000000) := by
  have h := checkLog_sound (w := (118965090369 / 618965090369)) (n := 12)
    (lo := (77848223 / 200000000)) (hi := (97310279 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368965090369 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(368965090369 / 250000000000) = 1/(250000000000 / 368965090369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5877 : Bounds (77848223 / 200000000) (97310279 / 250000000) (Real.log (368965090369 / 250000000000)) := by
  have h := reflection_log_5877_neg
  have he : Real.log (368965090369 / 250000000000) = -Real.log (250000000000 / 368965090369) := by
    rw [show ((368965090369 / 250000000000) : ℝ) = ((250000000000 / 368965090369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5878_neg : (87942107 / 500000000) ≤ -Real.log (10000 / 11923) ∧
    -Real.log (10000 / 11923) ≤ (35176843 / 200000000) := by
  have h := checkLog_sound (w := (1923 / 21923)) (n := 12)
    (lo := (87942107 / 500000000)) (hi := (35176843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11923 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11923 / 10000) = 1/(10000 / 11923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5878 : Bounds (87942107 / 500000000) (35176843 / 200000000) (Real.log (11923 / 10000)) := by
  have h := reflection_log_5878_neg
  have he : Real.log (11923 / 10000) = -Real.log (10000 / 11923) := by
    rw [show ((11923 / 10000) : ℝ) = ((10000 / 11923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5879_neg : (6673893 / 31250000) ≤ -Real.log (8077 / 10000) ∧
    -Real.log (8077 / 10000) ≤ (213564577 / 1000000000) := by
  have h := checkLog_sound (w := (1923 / 18077)) (n := 12)
    (lo := (6673893 / 31250000)) (hi := (213564577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8077) = 1/(8077 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5879 : Bounds (-213564577 / 1000000000) (-6673893 / 31250000) (Real.log (8077 / 10000)) := by
  have h := reflection_log_5879_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5880_neg : (192281 / 1000000000) ≤ -Real.log (10000000 / 10001923) ∧
    -Real.log (10000000 / 10001923) ≤ (96141 / 500000000) := by
  have h := checkLog_sound (w := (1923 / 20001923)) (n := 12)
    (lo := (192281 / 1000000000)) (hi := (96141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001923 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001923 / 10000000) = 1/(10000000 / 10001923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5880 : Bounds (192281 / 1000000000) (96141 / 500000000) (Real.log (10001923 / 10000000)) := by
  have h := reflection_log_5880_neg
  have he : Real.log (10001923 / 10000000) = -Real.log (10000000 / 10001923) := by
    rw [show ((10001923 / 10000000) : ℝ) = ((10000000 / 10001923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5881_neg : (96159 / 500000000) ≤ -Real.log (9998077 / 10000000) ∧
    -Real.log (9998077 / 10000000) ≤ (192319 / 1000000000) := by
  have h := checkLog_sound (w := (1923 / 19998077)) (n := 12)
    (lo := (96159 / 500000000)) (hi := (192319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998077) = 1/(9998077 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5881 : Bounds (-192319 / 1000000000) (-96159 / 500000000) (Real.log (9998077 / 10000000)) := by
  have h := reflection_log_5881_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5882_neg : (9226099 / 100000000) ≤ -Real.log (1000000 / 1096651) ∧
    -Real.log (1000000 / 1096651) ≤ (92260991 / 1000000000) := by
  have h := checkLog_sound (w := (96651 / 2096651)) (n := 12)
    (lo := (9226099 / 100000000)) (hi := (92260991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096651 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096651 / 1000000) = 1/(1000000 / 1096651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5882 : Bounds (9226099 / 100000000) (92260991 / 1000000000) (Real.log (1096651 / 1000000)) := by
  have h := reflection_log_5882_neg
  have he : Real.log (1096651 / 1000000) = -Real.log (1000000 / 1096651) := by
    rw [show ((1096651 / 1000000) : ℝ) = ((1000000 / 1096651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5883_neg : (10164631 / 100000000) ≤ -Real.log (903349 / 1000000) ∧
    -Real.log (903349 / 1000000) ≤ (101646311 / 1000000000) := by
  have h := checkLog_sound (w := (96651 / 1903349)) (n := 12)
    (lo := (10164631 / 100000000)) (hi := (101646311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903349) = 1/(903349 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5883 : Bounds (-101646311 / 1000000000) (-10164631 / 100000000) (Real.log (903349 / 1000000)) := by
  have h := reflection_log_5883_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5884_neg : (92482549 / 1000000000) ≤ -Real.log (500000 / 548447) ∧
    -Real.log (500000 / 548447) ≤ (1849651 / 20000000) := by
  have h := checkLog_sound (w := (48447 / 1048447)) (n := 12)
    (lo := (92482549 / 1000000000)) (hi := (1849651 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548447 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548447 / 500000) = 1/(500000 / 548447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5884 : Bounds (92482549 / 1000000000) (1849651 / 20000000) (Real.log (548447 / 500000)) := by
  have h := reflection_log_5884_neg
  have he : Real.log (548447 / 500000) = -Real.log (500000 / 548447) := by
    rw [show ((548447 / 500000) : ℝ) = ((500000 / 548447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5885_neg : (20383069 / 200000000) ≤ -Real.log (451553 / 500000) ∧
    -Real.log (451553 / 500000) ≤ (50957673 / 500000000) := by
  have h := checkLog_sound (w := (48447 / 951553)) (n := 12)
    (lo := (20383069 / 200000000)) (hi := (50957673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451553) = 1/(451553 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5885 : Bounds (-50957673 / 500000000) (-20383069 / 200000000) (Real.log (451553 / 500000)) := by
  have h := reflection_log_5885_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5886_neg : (2358199 / 250000000) ≤ -Real.log (247652888191 / 250000000000) ∧
    -Real.log (247652888191 / 250000000000) ≤ (9432797 / 1000000000) := by
  have h := checkLog_sound (w := (2347111809 / 497652888191)) (n := 12)
    (lo := (2358199 / 250000000)) (hi := (9432797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247652888191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247652888191) = 1/(247652888191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5886 : Bounds (-9432797 / 1000000000) (-2358199 / 250000000) (Real.log (247652888191 / 250000000000)) := by
  have h := reflection_log_5886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5887_neg : (234633 / 25000000) ≤ -Real.log (990658584199 / 1000000000000) ∧
    -Real.log (990658584199 / 1000000000000) ≤ (9385321 / 1000000000) := by
  have h := checkLog_sound (w := (9341415801 / 1990658584199)) (n := 12)
    (lo := (234633 / 25000000)) (hi := (9385321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990658584199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990658584199) = 1/(990658584199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5887 : Bounds (-9385321 / 1000000000) (-234633 / 25000000) (Real.log (990658584199 / 1000000000000)) := by
  have h := reflection_log_5887_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
