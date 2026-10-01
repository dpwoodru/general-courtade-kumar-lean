import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6272_neg : (4877 / 25000000) ≤ -Real.log (10000000 / 10001951) ∧
    -Real.log (10000000 / 10001951) ≤ (195081 / 1000000000) := by
  have h := checkLog_sound (w := (1951 / 20001951)) (n := 12)
    (lo := (4877 / 25000000)) (hi := (195081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001951 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001951 / 10000000) = 1/(10000000 / 10001951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6272 : Bounds (4877 / 25000000) (195081 / 1000000000) (Real.log (10001951 / 10000000)) := by
  have h := reflection_log_6272_neg
  have he : Real.log (10001951 / 10000000) = -Real.log (10000000 / 10001951) := by
    rw [show ((10001951 / 10000000) : ℝ) = ((10000000 / 10001951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6273_neg : (195119 / 1000000000) ≤ -Real.log (9998049 / 10000000) ∧
    -Real.log (9998049 / 10000000) ≤ (2439 / 12500000) := by
  have h := checkLog_sound (w := (1951 / 19998049)) (n := 12)
    (lo := (195119 / 1000000000)) (hi := (2439 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998049) = 1/(9998049 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6273 : Bounds (-2439 / 12500000) (-195119 / 1000000000) (Real.log (9998049 / 10000000)) := by
  have h := reflection_log_6273_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6274_neg : (93562289 / 1000000000) ≤ -Real.log (1000000 / 1098079) ∧
    -Real.log (1000000 / 1098079) ≤ (9356229 / 100000000) := by
  have h := checkLog_sound (w := (98079 / 2098079)) (n := 12)
    (lo := (93562289 / 1000000000)) (hi := (9356229 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098079 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098079 / 1000000) = 1/(1000000 / 1098079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6274 : Bounds (93562289 / 1000000000) (9356229 / 100000000) (Real.log (1098079 / 1000000)) := by
  have h := reflection_log_6274_neg
  have he : Real.log (1098079 / 1000000) = -Real.log (1000000 / 1098079) := by
    rw [show ((1098079 / 1000000) : ℝ) = ((1000000 / 1098079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6275_neg : (20645669 / 200000000) ≤ -Real.log (901921 / 1000000) ∧
    -Real.log (901921 / 1000000) ≤ (51614173 / 500000000) := by
  have h := checkLog_sound (w := (98079 / 1901921)) (n := 12)
    (lo := (20645669 / 200000000)) (hi := (51614173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901921) = 1/(901921 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6275 : Bounds (-51614173 / 500000000) (-20645669 / 200000000) (Real.log (901921 / 1000000)) := by
  have h := reflection_log_6275_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6276_neg : (23446573 / 250000000) ≤ -Real.log (40000 / 43933) ∧
    -Real.log (40000 / 43933) ≤ (93786293 / 1000000000) := by
  have h := checkLog_sound (w := (3933 / 83933)) (n := 12)
    (lo := (23446573 / 250000000)) (hi := (93786293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43933 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43933 / 40000) = 1/(40000 / 43933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6276 : Bounds (23446573 / 250000000) (93786293 / 1000000000) (Real.log (43933 / 40000)) := by
  have h := reflection_log_6276_neg
  have he : Real.log (43933 / 40000) = -Real.log (40000 / 43933) := by
    rw [show ((43933 / 40000) : ℝ) = ((40000 / 43933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6277_neg : (51750567 / 500000000) ≤ -Real.log (36067 / 40000) ∧
    -Real.log (36067 / 40000) ≤ (20700227 / 200000000) := by
  have h := checkLog_sound (w := (3933 / 76067)) (n := 12)
    (lo := (51750567 / 500000000)) (hi := (20700227 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36067) = 1/(36067 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6277 : Bounds (-20700227 / 200000000) (-51750567 / 500000000) (Real.log (36067 / 40000)) := by
  have h := reflection_log_6277_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6278_neg : (4857421 / 500000000) ≤ -Real.log (1584531511 / 1600000000) ∧
    -Real.log (1584531511 / 1600000000) ≤ (9714843 / 1000000000) := by
  have h := checkLog_sound (w := (15468489 / 3184531511)) (n := 12)
    (lo := (4857421 / 500000000)) (hi := (9714843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1584531511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1584531511) = 1/(1584531511 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6278 : Bounds (-9714843 / 1000000000) (-4857421 / 500000000) (Real.log (1584531511 / 1600000000)) := by
  have h := reflection_log_6278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6279_neg : (1208257 / 125000000) ≤ -Real.log (990380509759 / 1000000000000) ∧
    -Real.log (990380509759 / 1000000000000) ≤ (9666057 / 1000000000) := by
  have h := checkLog_sound (w := (9619490241 / 1990380509759)) (n := 12)
    (lo := (1208257 / 125000000)) (hi := (9666057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990380509759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990380509759) = 1/(990380509759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6279 : Bounds (-9666057 / 1000000000) (-1208257 / 125000000) (Real.log (990380509759 / 1000000000000)) := by
  have h := reflection_log_6279_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6280_neg : (39358127 / 200000000) ≤ -Real.log (10000000000 / 12174891149) ∧
    -Real.log (10000000000 / 12174891149) ≤ (49197659 / 250000000) := by
  have h := checkLog_sound (w := (2174891149 / 22174891149)) (n := 12)
    (lo := (39358127 / 200000000)) (hi := (49197659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12174891149 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12174891149 / 10000000000) = 1/(10000000000 / 12174891149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6280 : Bounds (39358127 / 200000000) (49197659 / 250000000) (Real.log (12174891149 / 10000000000)) := by
  have h := reflection_log_6280_neg
  have he : Real.log (12174891149 / 10000000000) = -Real.log (10000000000 / 12174891149) := by
    rw [show ((12174891149 / 10000000000) : ℝ) = ((10000000000 / 12174891149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6281_neg : (98643713 / 500000000) ≤ -Real.log (250000000000 / 304523525661) ∧
    -Real.log (250000000000 / 304523525661) ≤ (197287427 / 1000000000) := by
  have h := checkLog_sound (w := (54523525661 / 554523525661)) (n := 12)
    (lo := (98643713 / 500000000)) (hi := (197287427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304523525661 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304523525661 / 250000000000) = 1/(250000000000 / 304523525661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6281 : Bounds (98643713 / 500000000) (197287427 / 1000000000) (Real.log (304523525661 / 250000000000)) := by
  have h := reflection_log_6281_neg
  have he : Real.log (304523525661 / 250000000000) = -Real.log (250000000000 / 304523525661) := by
    rw [show ((304523525661 / 250000000000) : ℝ) = ((250000000000 / 304523525661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6282_neg : (197529593 / 500000000) ≤ -Real.log (125000000000 / 185559006211) ∧
    -Real.log (125000000000 / 185559006211) ≤ (395059187 / 1000000000) := by
  have h := checkLog_sound (w := (60559006211 / 310559006211)) (n := 12)
    (lo := (197529593 / 500000000)) (hi := (395059187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185559006211 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185559006211 / 125000000000) = 1/(125000000000 / 185559006211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6282 : Bounds (197529593 / 500000000) (395059187 / 1000000000) (Real.log (185559006211 / 125000000000)) := by
  have h := reflection_log_6282_neg
  have he : Real.log (185559006211 / 125000000000) = -Real.log (125000000000 / 185559006211) := by
    rw [show ((185559006211 / 125000000000) : ℝ) = ((125000000000 / 185559006211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6283_neg : (49408387 / 125000000) ≤ -Real.log (500000000000 / 742390359051) ∧
    -Real.log (500000000000 / 742390359051) ≤ (395267097 / 1000000000) := by
  have h := checkLog_sound (w := (242390359051 / 1242390359051)) (n := 12)
    (lo := (49408387 / 125000000)) (hi := (395267097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742390359051 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742390359051 / 500000000000) = 1/(500000000000 / 742390359051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6283 : Bounds (49408387 / 125000000) (395267097 / 1000000000) (Real.log (742390359051 / 500000000000)) := by
  have h := reflection_log_6283_neg
  have he : Real.log (742390359051 / 500000000000) = -Real.log (500000000000 / 742390359051) := by
    rw [show ((742390359051 / 500000000000) : ℝ) = ((500000000000 / 742390359051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6284_neg : (35662707 / 200000000) ≤ -Real.log (625 / 747) ∧
    -Real.log (625 / 747) ≤ (2786149 / 15625000) := by
  have h := checkLog_sound (w := (61 / 686)) (n := 12)
    (lo := (35662707 / 200000000)) (hi := (2786149 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747 / 625) = 1/(625 / 747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6284 : Bounds (35662707 / 200000000) (2786149 / 15625000) (Real.log (747 / 625)) := by
  have h := reflection_log_6284_neg
  have he : Real.log (747 / 625) = -Real.log (625 / 747) := by
    rw [show ((747 / 625) : ℝ) = ((625 / 747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6285_neg : (217161479 / 1000000000) ≤ -Real.log (503 / 625) ∧
    -Real.log (503 / 625) ≤ (5429037 / 25000000) := by
  have h := checkLog_sound (w := (61 / 564)) (n := 12)
    (lo := (217161479 / 1000000000)) (hi := (5429037 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 503) = 1/(503 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6285 : Bounds (-5429037 / 25000000) (-217161479 / 1000000000) (Real.log (503 / 625)) := by
  have h := reflection_log_6285_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6286_neg : (9759 / 50000000) ≤ -Real.log (312500 / 312561) ∧
    -Real.log (312500 / 312561) ≤ (195181 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 625061)) (n := 12)
    (lo := (9759 / 50000000)) (hi := (195181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312561 / 312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312561 / 312500) = 1/(312500 / 312561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6286 : Bounds (9759 / 50000000) (195181 / 1000000000) (Real.log (312561 / 312500)) := by
  have h := reflection_log_6286_neg
  have he : Real.log (312561 / 312500) = -Real.log (312500 / 312561) := by
    rw [show ((312561 / 312500) : ℝ) = ((312500 / 312561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6287_neg : (195219 / 1000000000) ≤ -Real.log (312439 / 312500) ∧
    -Real.log (312439 / 312500) ≤ (9761 / 50000000) := by
  have h := checkLog_sound (w := (61 / 624939)) (n := 12)
    (lo := (195219 / 1000000000)) (hi := (9761 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312500 / 312439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312500 / 312439) = 1/(312439 / 312500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6287 : Bounds (-9761 / 50000000) (-195219 / 1000000000) (Real.log (312439 / 312500)) := by
  have h := reflection_log_6287_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6288_neg : (93608733 / 1000000000) ≤ -Real.log (100000 / 109813) ∧
    -Real.log (100000 / 109813) ≤ (46804367 / 500000000) := by
  have h := checkLog_sound (w := (9813 / 209813)) (n := 12)
    (lo := (93608733 / 1000000000)) (hi := (46804367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109813 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109813 / 100000) = 1/(100000 / 109813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6288 : Bounds (93608733 / 1000000000) (46804367 / 500000000) (Real.log (109813 / 100000)) := by
  have h := reflection_log_6288_neg
  have he : Real.log (109813 / 100000) = -Real.log (100000 / 109813) := by
    rw [show ((109813 / 100000) : ℝ) = ((100000 / 109813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6289_neg : (103284893 / 1000000000) ≤ -Real.log (90187 / 100000) ∧
    -Real.log (90187 / 100000) ≤ (51642447 / 500000000) := by
  have h := checkLog_sound (w := (9813 / 190187)) (n := 12)
    (lo := (103284893 / 1000000000)) (hi := (51642447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90187) = 1/(90187 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6289 : Bounds (-51642447 / 500000000) (-103284893 / 1000000000) (Real.log (90187 / 100000)) := by
  have h := reflection_log_6289_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6290_neg : (3753309 / 40000000) ≤ -Real.log (125000 / 137297) ∧
    -Real.log (125000 / 137297) ≤ (46916363 / 500000000) := by
  have h := checkLog_sound (w := (12297 / 262297)) (n := 12)
    (lo := (3753309 / 40000000)) (hi := (46916363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137297 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137297 / 125000) = 1/(125000 / 137297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6290 : Bounds (3753309 / 40000000) (46916363 / 500000000) (Real.log (137297 / 125000)) := by
  have h := reflection_log_6290_neg
  have he : Real.log (137297 / 125000) = -Real.log (125000 / 137297) := by
    rw [show ((137297 / 125000) : ℝ) = ((125000 / 137297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6291_neg : (103557697 / 1000000000) ≤ -Real.log (112703 / 125000) ∧
    -Real.log (112703 / 125000) ≤ (51778849 / 500000000) := by
  have h := checkLog_sound (w := (12297 / 237703)) (n := 12)
    (lo := (103557697 / 1000000000)) (hi := (51778849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112703) = 1/(112703 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6291 : Bounds (-51778849 / 500000000) (-103557697 / 1000000000) (Real.log (112703 / 125000)) := by
  have h := reflection_log_6291_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6292_neg : (9724971 / 1000000000) ≤ -Real.log (15473783791 / 15625000000) ∧
    -Real.log (15473783791 / 15625000000) ≤ (2431243 / 250000000) := by
  have h := checkLog_sound (w := (151216209 / 31098783791)) (n := 12)
    (lo := (9724971 / 1000000000)) (hi := (2431243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15473783791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15473783791) = 1/(15473783791 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6292 : Bounds (-2431243 / 250000000) (-9724971 / 1000000000) (Real.log (15473783791 / 15625000000)) := by
  have h := reflection_log_6292_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6293_neg : (15119 / 1562500) ≤ -Real.log (9903705031 / 10000000000) ∧
    -Real.log (9903705031 / 10000000000) ≤ (9676161 / 1000000000) := by
  have h := checkLog_sound (w := (96294969 / 19903705031)) (n := 12)
    (lo := (15119 / 1562500)) (hi := (9676161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9903705031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9903705031) = 1/(9903705031 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6293 : Bounds (-9676161 / 1000000000) (-15119 / 1562500) (Real.log (9903705031 / 10000000000)) := by
  have h := reflection_log_6293_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6294_neg : (98446813 / 500000000) ≤ -Real.log (250000000000 / 304403628017) ∧
    -Real.log (250000000000 / 304403628017) ≤ (196893627 / 1000000000) := by
  have h := checkLog_sound (w := (54403628017 / 554403628017)) (n := 12)
    (lo := (98446813 / 500000000)) (hi := (196893627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304403628017 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304403628017 / 250000000000) = 1/(250000000000 / 304403628017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6294 : Bounds (98446813 / 500000000) (196893627 / 1000000000) (Real.log (304403628017 / 250000000000)) := by
  have h := reflection_log_6294_neg
  have he : Real.log (304403628017 / 250000000000) = -Real.log (250000000000 / 304403628017) := by
    rw [show ((304403628017 / 250000000000) : ℝ) = ((250000000000 / 304403628017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6295_neg : (98695211 / 500000000) ≤ -Real.log (500000000000 / 609109784123) ∧
    -Real.log (500000000000 / 609109784123) ≤ (197390423 / 1000000000) := by
  have h := checkLog_sound (w := (109109784123 / 1109109784123)) (n := 12)
    (lo := (98695211 / 500000000)) (hi := (197390423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609109784123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609109784123 / 500000000000) = 1/(500000000000 / 609109784123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6295 : Bounds (98695211 / 500000000) (197390423 / 1000000000) (Real.log (609109784123 / 500000000000)) := by
  have h := reflection_log_6295_neg
  have he : Real.log (609109784123 / 500000000000) = -Real.log (500000000000 / 609109784123) := by
    rw [show ((609109784123 / 500000000000) : ℝ) = ((500000000000 / 609109784123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6296_neg : (49408387 / 125000000) ≤ -Real.log (10000000000 / 14847807181) ∧
    -Real.log (10000000000 / 14847807181) ≤ (395267097 / 1000000000) := by
  have h := checkLog_sound (w := (4847807181 / 24847807181)) (n := 12)
    (lo := (49408387 / 125000000)) (hi := (395267097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14847807181 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14847807181 / 10000000000) = 1/(10000000000 / 14847807181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6296 : Bounds (49408387 / 125000000) (395267097 / 1000000000) (Real.log (14847807181 / 10000000000)) := by
  have h := reflection_log_6296_neg
  have he : Real.log (14847807181 / 10000000000) = -Real.log (10000000000 / 14847807181) := by
    rw [show ((14847807181 / 10000000000) : ℝ) = ((10000000000 / 14847807181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6297_neg : (79095003 / 200000000) ≤ -Real.log (500000000000 / 742544731611) ∧
    -Real.log (500000000000 / 742544731611) ≤ (49434377 / 125000000) := by
  have h := checkLog_sound (w := (242544731611 / 1242544731611)) (n := 12)
    (lo := (79095003 / 200000000)) (hi := (49434377 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742544731611 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742544731611 / 500000000000) = 1/(500000000000 / 742544731611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6297 : Bounds (79095003 / 200000000) (49434377 / 125000000) (Real.log (742544731611 / 500000000000)) := by
  have h := reflection_log_6297_neg
  have he : Real.log (742544731611 / 500000000000) = -Real.log (500000000000 / 742544731611) := by
    rw [show ((742544731611 / 500000000000) : ℝ) = ((500000000000 / 742544731611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6298_neg : (178397199 / 1000000000) ≤ -Real.log (10000 / 11953) ∧
    -Real.log (10000 / 11953) ≤ (445993 / 2500000) := by
  have h := checkLog_sound (w := (1953 / 21953)) (n := 12)
    (lo := (178397199 / 1000000000)) (hi := (445993 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11953 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11953 / 10000) = 1/(10000 / 11953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6298 : Bounds (178397199 / 1000000000) (445993 / 2500000) (Real.log (11953 / 10000)) := by
  have h := reflection_log_6298_neg
  have he : Real.log (11953 / 10000) = -Real.log (10000 / 11953) := by
    rw [show ((11953 / 10000) : ℝ) = ((10000 / 11953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6299_neg : (217285741 / 1000000000) ≤ -Real.log (8047 / 10000) ∧
    -Real.log (8047 / 10000) ≤ (108642871 / 500000000) := by
  have h := checkLog_sound (w := (1953 / 18047)) (n := 12)
    (lo := (217285741 / 1000000000)) (hi := (108642871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8047) = 1/(8047 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6299 : Bounds (-108642871 / 500000000) (-217285741 / 1000000000) (Real.log (8047 / 10000)) := by
  have h := reflection_log_6299_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6300_neg : (2441 / 12500000) ≤ -Real.log (10000000 / 10001953) ∧
    -Real.log (10000000 / 10001953) ≤ (195281 / 1000000000) := by
  have h := checkLog_sound (w := (1953 / 20001953)) (n := 12)
    (lo := (2441 / 12500000)) (hi := (195281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001953 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001953 / 10000000) = 1/(10000000 / 10001953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6300 : Bounds (2441 / 12500000) (195281 / 1000000000) (Real.log (10001953 / 10000000)) := by
  have h := reflection_log_6300_neg
  have he : Real.log (10001953 / 10000000) = -Real.log (10000000 / 10001953) := by
    rw [show ((10001953 / 10000000) : ℝ) = ((10000000 / 10001953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6301_neg : (195319 / 1000000000) ≤ -Real.log (9998047 / 10000000) ∧
    -Real.log (9998047 / 10000000) ≤ (4883 / 25000000) := by
  have h := checkLog_sound (w := (1953 / 19998047)) (n := 12)
    (lo := (195319 / 1000000000)) (hi := (4883 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998047) = 1/(9998047 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6301 : Bounds (-4883 / 25000000) (-195319 / 1000000000) (Real.log (9998047 / 10000000)) := by
  have h := reflection_log_6301_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6302_neg : (46827587 / 500000000) ≤ -Real.log (1000000 / 1098181) ∧
    -Real.log (1000000 / 1098181) ≤ (3746207 / 40000000) := by
  have h := checkLog_sound (w := (98181 / 2098181)) (n := 12)
    (lo := (46827587 / 500000000)) (hi := (3746207 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098181 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098181 / 1000000) = 1/(1000000 / 1098181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6302 : Bounds (46827587 / 500000000) (3746207 / 40000000) (Real.log (1098181 / 1000000)) := by
  have h := reflection_log_6302_neg
  have he : Real.log (1098181 / 1000000) = -Real.log (1000000 / 1098181) := by
    rw [show ((1098181 / 1000000) : ℝ) = ((1000000 / 1098181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6303_neg : (25835361 / 250000000) ≤ -Real.log (901819 / 1000000) ∧
    -Real.log (901819 / 1000000) ≤ (20668289 / 200000000) := by
  have h := checkLog_sound (w := (98181 / 1901819)) (n := 12)
    (lo := (25835361 / 250000000)) (hi := (20668289 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901819) = 1/(901819 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6303 : Bounds (-20668289 / 200000000) (-25835361 / 250000000) (Real.log (901819 / 1000000)) := by
  have h := reflection_log_6303_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6304_neg : (23469789 / 250000000) ≤ -Real.log (1000000 / 1098427) ∧
    -Real.log (1000000 / 1098427) ≤ (93879157 / 1000000000) := by
  have h := checkLog_sound (w := (98427 / 2098427)) (n := 12)
    (lo := (23469789 / 250000000)) (hi := (93879157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098427 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098427 / 1000000) = 1/(1000000 / 1098427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6304 : Bounds (23469789 / 250000000) (93879157 / 1000000000) (Real.log (1098427 / 1000000)) := by
  have h := reflection_log_6304_neg
  have he : Real.log (1098427 / 1000000) = -Real.log (1000000 / 1098427) := by
    rw [show ((1098427 / 1000000) : ℝ) = ((1000000 / 1098427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6305_neg : (103614263 / 1000000000) ≤ -Real.log (901573 / 1000000) ∧
    -Real.log (901573 / 1000000) ≤ (12951783 / 125000000) := by
  have h := checkLog_sound (w := (98427 / 1901573)) (n := 12)
    (lo := (103614263 / 1000000000)) (hi := (12951783 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901573) = 1/(901573 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6305 : Bounds (-12951783 / 125000000) (-103614263 / 1000000000) (Real.log (901573 / 1000000)) := by
  have h := reflection_log_6305_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6306_neg : (9735107 / 1000000000) ≤ -Real.log (990312125671 / 1000000000000) ∧
    -Real.log (990312125671 / 1000000000000) ≤ (2433777 / 250000000) := by
  have h := checkLog_sound (w := (9687874329 / 1990312125671)) (n := 12)
    (lo := (9735107 / 1000000000)) (hi := (2433777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990312125671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990312125671) = 1/(990312125671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6306 : Bounds (-2433777 / 250000000) (-9735107 / 1000000000) (Real.log (990312125671 / 1000000000000)) := by
  have h := reflection_log_6306_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6307_neg : (9686269 / 1000000000) ≤ -Real.log (990360491239 / 1000000000000) ∧
    -Real.log (990360491239 / 1000000000000) ≤ (968627 / 100000000) := by
  have h := checkLog_sound (w := (9639508761 / 1990360491239)) (n := 12)
    (lo := (9686269 / 1000000000)) (hi := (968627 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990360491239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990360491239) = 1/(990360491239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6307 : Bounds (-968627 / 100000000) (-9686269 / 1000000000) (Real.log (990360491239 / 1000000000000)) := by
  have h := reflection_log_6307_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6308_neg : (98498309 / 500000000) ≤ -Real.log (50000000000 / 60886996171) ∧
    -Real.log (50000000000 / 60886996171) ≤ (196996619 / 1000000000) := by
  have h := checkLog_sound (w := (10886996171 / 110886996171)) (n := 12)
    (lo := (98498309 / 500000000)) (hi := (196996619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60886996171 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60886996171 / 50000000000) = 1/(50000000000 / 60886996171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6308 : Bounds (98498309 / 500000000) (196996619 / 1000000000) (Real.log (60886996171 / 50000000000)) := by
  have h := reflection_log_6308_neg
  have he : Real.log (60886996171 / 50000000000) = -Real.log (50000000000 / 60886996171) := by
    rw [show ((60886996171 / 50000000000) : ℝ) = ((50000000000 / 60886996171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6309_neg : (197493419 / 1000000000) ≤ -Real.log (250000000000 / 304586262011) ∧
    -Real.log (250000000000 / 304586262011) ≤ (9874671 / 50000000) := by
  have h := checkLog_sound (w := (54586262011 / 554586262011)) (n := 12)
    (lo := (197493419 / 1000000000)) (hi := (9874671 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304586262011 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304586262011 / 250000000000) = 1/(250000000000 / 304586262011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6309 : Bounds (197493419 / 1000000000) (9874671 / 50000000) (Real.log (304586262011 / 250000000000)) := by
  have h := reflection_log_6309_neg
  have he : Real.log (304586262011 / 250000000000) = -Real.log (250000000000 / 304586262011) := by
    rw [show ((304586262011 / 250000000000) : ℝ) = ((250000000000 / 304586262011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6310_neg : (79095003 / 200000000) ≤ -Real.log (50000000000 / 74254473161) ∧
    -Real.log (50000000000 / 74254473161) ≤ (49434377 / 125000000) := by
  have h := checkLog_sound (w := (24254473161 / 124254473161)) (n := 12)
    (lo := (79095003 / 200000000)) (hi := (49434377 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74254473161 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74254473161 / 50000000000) = 1/(50000000000 / 74254473161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6310 : Bounds (79095003 / 200000000) (49434377 / 125000000) (Real.log (74254473161 / 50000000000)) := by
  have h := reflection_log_6310_neg
  have he : Real.log (74254473161 / 50000000000) = -Real.log (50000000000 / 74254473161) := by
    rw [show ((74254473161 / 50000000000) : ℝ) = ((50000000000 / 74254473161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6311_neg : (395682941 / 1000000000) ≤ -Real.log (250000000000 / 371349571269) ∧
    -Real.log (250000000000 / 371349571269) ≤ (197841471 / 500000000) := by
  have h := checkLog_sound (w := (121349571269 / 621349571269)) (n := 12)
    (lo := (395682941 / 1000000000)) (hi := (197841471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((371349571269 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(371349571269 / 250000000000) = 1/(250000000000 / 371349571269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6311 : Bounds (395682941 / 1000000000) (197841471 / 500000000) (Real.log (371349571269 / 250000000000)) := by
  have h := reflection_log_6311_neg
  have he : Real.log (371349571269 / 250000000000) = -Real.log (250000000000 / 371349571269) := by
    rw [show ((371349571269 / 250000000000) : ℝ) = ((250000000000 / 371349571269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6312_neg : (178480857 / 1000000000) ≤ -Real.log (5000 / 5977) ∧
    -Real.log (5000 / 5977) ≤ (89240429 / 500000000) := by
  have h := checkLog_sound (w := (977 / 10977)) (n := 12)
    (lo := (178480857 / 1000000000)) (hi := (89240429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5977 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5977 / 5000) = 1/(5000 / 5977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6312 : Bounds (178480857 / 1000000000) (89240429 / 500000000) (Real.log (5977 / 5000)) := by
  have h := reflection_log_6312_neg
  have he : Real.log (5977 / 5000) = -Real.log (5000 / 5977) := by
    rw [show ((5977 / 5000) : ℝ) = ((5000 / 5977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6313_neg : (217410019 / 1000000000) ≤ -Real.log (4023 / 5000) ∧
    -Real.log (4023 / 5000) ≤ (10870501 / 50000000) := by
  have h := checkLog_sound (w := (977 / 9023)) (n := 12)
    (lo := (217410019 / 1000000000)) (hi := (10870501 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4023) = 1/(4023 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6313 : Bounds (-10870501 / 50000000) (-217410019 / 1000000000) (Real.log (4023 / 5000)) := by
  have h := reflection_log_6313_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6314_neg : (9769 / 50000000) ≤ -Real.log (5000000 / 5000977) ∧
    -Real.log (5000000 / 5000977) ≤ (195381 / 1000000000) := by
  have h := checkLog_sound (w := (977 / 10000977)) (n := 12)
    (lo := (9769 / 50000000)) (hi := (195381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000977 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000977 / 5000000) = 1/(5000000 / 5000977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6314 : Bounds (9769 / 50000000) (195381 / 1000000000) (Real.log (5000977 / 5000000)) := by
  have h := reflection_log_6314_neg
  have he : Real.log (5000977 / 5000000) = -Real.log (5000000 / 5000977) := by
    rw [show ((5000977 / 5000000) : ℝ) = ((5000000 / 5000977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6315_neg : (195419 / 1000000000) ≤ -Real.log (4999023 / 5000000) ∧
    -Real.log (4999023 / 5000000) ≤ (9771 / 50000000) := by
  have h := checkLog_sound (w := (977 / 9999023)) (n := 12)
    (lo := (195419 / 1000000000)) (hi := (9771 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999023) = 1/(4999023 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6315 : Bounds (-9771 / 50000000) (-195419 / 1000000000) (Real.log (4999023 / 5000000)) := by
  have h := reflection_log_6315_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6316_neg : (46850807 / 500000000) ≤ -Real.log (125000 / 137279) ∧
    -Real.log (125000 / 137279) ≤ (18740323 / 200000000) := by
  have h := checkLog_sound (w := (12279 / 262279)) (n := 12)
    (lo := (46850807 / 500000000)) (hi := (18740323 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137279 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137279 / 125000) = 1/(125000 / 137279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6316 : Bounds (46850807 / 500000000) (18740323 / 200000000) (Real.log (137279 / 125000)) := by
  have h := reflection_log_6316_neg
  have he : Real.log (137279 / 125000) = -Real.log (125000 / 137279) := by
    rw [show ((137279 / 125000) : ℝ) = ((125000 / 137279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6317_neg : (51698999 / 500000000) ≤ -Real.log (112721 / 125000) ∧
    -Real.log (112721 / 125000) ≤ (103397999 / 1000000000) := by
  have h := checkLog_sound (w := (12279 / 237721)) (n := 12)
    (lo := (51698999 / 500000000)) (hi := (103397999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112721) = 1/(112721 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6317 : Bounds (-103397999 / 1000000000) (-51698999 / 500000000) (Real.log (112721 / 125000)) := by
  have h := reflection_log_6317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6318_neg : (18785117 / 200000000) ≤ -Real.log (500000 / 549239) ∧
    -Real.log (500000 / 549239) ≤ (46962793 / 500000000) := by
  have h := checkLog_sound (w := (49239 / 1049239)) (n := 12)
    (lo := (18785117 / 200000000)) (hi := (46962793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549239 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549239 / 500000) = 1/(500000 / 549239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6318 : Bounds (18785117 / 200000000) (46962793 / 500000000) (Real.log (549239 / 500000)) := by
  have h := reflection_log_6318_neg
  have he : Real.log (549239 / 500000) = -Real.log (500000 / 549239) := by
    rw [show ((549239 / 500000) : ℝ) = ((500000 / 549239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6319_neg : (6479427 / 62500000) ≤ -Real.log (450761 / 500000) ∧
    -Real.log (450761 / 500000) ≤ (103670833 / 1000000000) := by
  have h := checkLog_sound (w := (49239 / 950761)) (n := 12)
    (lo := (6479427 / 62500000)) (hi := (103670833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450761) = 1/(450761 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6319 : Bounds (-103670833 / 1000000000) (-6479427 / 62500000) (Real.log (450761 / 500000)) := by
  have h := reflection_log_6319_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6320_neg : (9745247 / 1000000000) ≤ -Real.log (247575520879 / 250000000000) ∧
    -Real.log (247575520879 / 250000000000) ≤ (304539 / 31250000) := by
  have h := checkLog_sound (w := (2424479121 / 497575520879)) (n := 12)
    (lo := (9745247 / 1000000000)) (hi := (304539 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247575520879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247575520879) = 1/(247575520879 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6320 : Bounds (-304539 / 31250000) (-9745247 / 1000000000) (Real.log (247575520879 / 250000000000)) := by
  have h := reflection_log_6320_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6321_neg : (75753 / 7812500) ≤ -Real.log (15474226159 / 15625000000) ∧
    -Real.log (15474226159 / 15625000000) ≤ (1939277 / 200000000) := by
  have h := checkLog_sound (w := (150773841 / 31099226159)) (n := 12)
    (lo := (75753 / 7812500)) (hi := (1939277 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15474226159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15474226159) = 1/(15474226159 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6321 : Bounds (-1939277 / 200000000) (-75753 / 7812500) (Real.log (15474226159 / 15625000000)) := by
  have h := reflection_log_6321_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6322_neg : (49274903 / 250000000) ≤ -Real.log (500000000000 / 608932674479) ∧
    -Real.log (500000000000 / 608932674479) ≤ (197099613 / 1000000000) := by
  have h := checkLog_sound (w := (108932674479 / 1108932674479)) (n := 12)
    (lo := (49274903 / 250000000)) (hi := (197099613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608932674479 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608932674479 / 500000000000) = 1/(500000000000 / 608932674479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6322 : Bounds (49274903 / 250000000) (197099613 / 1000000000) (Real.log (608932674479 / 500000000000)) := by
  have h := reflection_log_6322_neg
  have he : Real.log (608932674479 / 500000000000) = -Real.log (500000000000 / 608932674479) := by
    rw [show ((608932674479 / 500000000000) : ℝ) = ((500000000000 / 608932674479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6323_neg : (98798209 / 500000000) ≤ -Real.log (25000000000 / 30461763551) ∧
    -Real.log (25000000000 / 30461763551) ≤ (197596419 / 1000000000) := by
  have h := checkLog_sound (w := (5461763551 / 55461763551)) (n := 12)
    (lo := (98798209 / 500000000)) (hi := (197596419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30461763551 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30461763551 / 25000000000) = 1/(25000000000 / 30461763551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6323 : Bounds (98798209 / 500000000) (197596419 / 1000000000) (Real.log (30461763551 / 25000000000)) := by
  have h := reflection_log_6323_neg
  have he : Real.log (30461763551 / 25000000000) = -Real.log (25000000000 / 30461763551) := by
    rw [show ((30461763551 / 25000000000) : ℝ) = ((25000000000 / 30461763551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6324_neg : (395682941 / 1000000000) ≤ -Real.log (500000000000 / 742699142537) ∧
    -Real.log (500000000000 / 742699142537) ≤ (197841471 / 500000000) := by
  have h := checkLog_sound (w := (242699142537 / 1242699142537)) (n := 12)
    (lo := (395682941 / 1000000000)) (hi := (197841471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742699142537 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742699142537 / 500000000000) = 1/(500000000000 / 742699142537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6324 : Bounds (395682941 / 1000000000) (197841471 / 500000000) (Real.log (742699142537 / 500000000000)) := by
  have h := reflection_log_6324_neg
  have he : Real.log (742699142537 / 500000000000) = -Real.log (500000000000 / 742699142537) := by
    rw [show ((742699142537 / 500000000000) : ℝ) = ((500000000000 / 742699142537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6325_neg : (98972719 / 250000000) ≤ -Real.log (500000000000 / 742853591847) ∧
    -Real.log (500000000000 / 742853591847) ≤ (395890877 / 1000000000) := by
  have h := checkLog_sound (w := (242853591847 / 1242853591847)) (n := 12)
    (lo := (98972719 / 250000000)) (hi := (395890877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742853591847 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742853591847 / 500000000000) = 1/(500000000000 / 742853591847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6325 : Bounds (98972719 / 250000000) (395890877 / 1000000000) (Real.log (742853591847 / 500000000000)) := by
  have h := reflection_log_6325_neg
  have he : Real.log (742853591847 / 500000000000) = -Real.log (500000000000 / 742853591847) := by
    rw [show ((742853591847 / 500000000000) : ℝ) = ((500000000000 / 742853591847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6326_neg : (178564507 / 1000000000) ≤ -Real.log (2000 / 2391) ∧
    -Real.log (2000 / 2391) ≤ (44641127 / 250000000) := by
  have h := checkLog_sound (w := (391 / 4391)) (n := 12)
    (lo := (178564507 / 1000000000)) (hi := (44641127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2391 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2391 / 2000) = 1/(2000 / 2391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6326 : Bounds (178564507 / 1000000000) (44641127 / 250000000) (Real.log (2391 / 2000)) := by
  have h := reflection_log_6326_neg
  have he : Real.log (2391 / 2000) = -Real.log (2000 / 2391) := by
    rw [show ((2391 / 2000) : ℝ) = ((2000 / 2391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6327_neg : (27191789 / 125000000) ≤ -Real.log (1609 / 2000) ∧
    -Real.log (1609 / 2000) ≤ (217534313 / 1000000000) := by
  have h := checkLog_sound (w := (391 / 3609)) (n := 12)
    (lo := (27191789 / 125000000)) (hi := (217534313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1609) = 1/(1609 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6327 : Bounds (-217534313 / 1000000000) (-27191789 / 125000000) (Real.log (1609 / 2000)) := by
  have h := reflection_log_6327_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6328_neg : (4887 / 25000000) ≤ -Real.log (2000000 / 2000391) ∧
    -Real.log (2000000 / 2000391) ≤ (195481 / 1000000000) := by
  have h := checkLog_sound (w := (391 / 4000391)) (n := 12)
    (lo := (4887 / 25000000)) (hi := (195481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000391 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000391 / 2000000) = 1/(2000000 / 2000391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6328 : Bounds (4887 / 25000000) (195481 / 1000000000) (Real.log (2000391 / 2000000)) := by
  have h := reflection_log_6328_neg
  have he : Real.log (2000391 / 2000000) = -Real.log (2000000 / 2000391) := by
    rw [show ((2000391 / 2000000) : ℝ) = ((2000000 / 2000391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6329_neg : (195519 / 1000000000) ≤ -Real.log (1999609 / 2000000) ∧
    -Real.log (1999609 / 2000000) ≤ (611 / 3125000) := by
  have h := checkLog_sound (w := (391 / 3999609)) (n := 12)
    (lo := (195519 / 1000000000)) (hi := (611 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999609) = 1/(1999609 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6329 : Bounds (-611 / 3125000) (-195519 / 1000000000) (Real.log (1999609 / 2000000)) := by
  have h := reflection_log_6329_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6330_neg : (93748051 / 1000000000) ≤ -Real.log (1000000 / 1098283) ∧
    -Real.log (1000000 / 1098283) ≤ (23437013 / 250000000) := by
  have h := checkLog_sound (w := (98283 / 2098283)) (n := 12)
    (lo := (93748051 / 1000000000)) (hi := (23437013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098283 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098283 / 1000000) = 1/(1000000 / 1098283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6330 : Bounds (93748051 / 1000000000) (23437013 / 250000000) (Real.log (1098283 / 1000000)) := by
  have h := reflection_log_6330_neg
  have he : Real.log (1098283 / 1000000) = -Real.log (1000000 / 1098283) := by
    rw [show ((1098283 / 1000000) : ℝ) = ((1000000 / 1098283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6331_neg : (20690911 / 200000000) ≤ -Real.log (901717 / 1000000) ∧
    -Real.log (901717 / 1000000) ≤ (25863639 / 250000000) := by
  have h := checkLog_sound (w := (98283 / 1901717)) (n := 12)
    (lo := (20690911 / 200000000)) (hi := (25863639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901717) = 1/(901717 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6331 : Bounds (-25863639 / 250000000) (-20690911 / 200000000) (Real.log (901717 / 1000000)) := by
  have h := reflection_log_6331_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6332_neg : (23493003 / 250000000) ≤ -Real.log (1000000 / 1098529) ∧
    -Real.log (1000000 / 1098529) ≤ (93972013 / 1000000000) := by
  have h := checkLog_sound (w := (98529 / 2098529)) (n := 12)
    (lo := (23493003 / 250000000)) (hi := (93972013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098529 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098529 / 1000000) = 1/(1000000 / 1098529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6332 : Bounds (23493003 / 250000000) (93972013 / 1000000000) (Real.log (1098529 / 1000000)) := by
  have h := reflection_log_6332_neg
  have he : Real.log (1098529 / 1000000) = -Real.log (1000000 / 1098529) := by
    rw [show ((1098529 / 1000000) : ℝ) = ((1000000 / 1098529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6333_neg : (20745481 / 200000000) ≤ -Real.log (901471 / 1000000) ∧
    -Real.log (901471 / 1000000) ≤ (51863703 / 500000000) := by
  have h := checkLog_sound (w := (98529 / 1901471)) (n := 12)
    (lo := (20745481 / 200000000)) (hi := (51863703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901471) = 1/(901471 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6333 : Bounds (-51863703 / 500000000) (-20745481 / 200000000) (Real.log (901471 / 1000000)) := by
  have h := reflection_log_6333_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6334_neg : (9755393 / 1000000000) ≤ -Real.log (990292036159 / 1000000000000) ∧
    -Real.log (990292036159 / 1000000000000) ≤ (4877697 / 500000000) := by
  have h := checkLog_sound (w := (9707963841 / 1990292036159)) (n := 12)
    (lo := (9755393 / 1000000000)) (hi := (4877697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990292036159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990292036159) = 1/(990292036159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6334 : Bounds (-4877697 / 500000000) (-9755393 / 1000000000) (Real.log (990292036159 / 1000000000000)) := by
  have h := reflection_log_6334_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6335_neg : (1213313 / 125000000) ≤ -Real.log (990340451911 / 1000000000000) ∧
    -Real.log (990340451911 / 1000000000000) ≤ (1941301 / 200000000) := by
  have h := checkLog_sound (w := (9659548089 / 1990340451911)) (n := 12)
    (lo := (1213313 / 125000000)) (hi := (1941301 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990340451911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990340451911) = 1/(990340451911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6335 : Bounds (-1941301 / 200000000) (-1213313 / 125000000) (Real.log (990340451911 / 1000000000000)) := by
  have h := reflection_log_6335_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
