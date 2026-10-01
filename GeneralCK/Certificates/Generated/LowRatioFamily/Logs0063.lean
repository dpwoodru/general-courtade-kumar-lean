import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4032_neg : (197353979 / 1000000000) ≤ -Real.log (8209 / 10000) ∧
    -Real.log (8209 / 10000) ≤ (9867699 / 50000000) := by
  have h := checkLog_sound (w := (1791 / 18209)) (n := 12)
    (lo := (197353979 / 1000000000)) (hi := (9867699 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8209) = 1/(8209 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4032 : Bounds (-9867699 / 50000000) (-197353979 / 1000000000) (Real.log (8209 / 10000)) := by
  have h := reflection_log_4032_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4033_neg : (179083 / 1000000000) ≤ -Real.log (10000000 / 10001791) ∧
    -Real.log (10000000 / 10001791) ≤ (44771 / 250000000) := by
  have h := checkLog_sound (w := (1791 / 20001791)) (n := 12)
    (lo := (179083 / 1000000000)) (hi := (44771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001791 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001791 / 10000000) = 1/(10000000 / 10001791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4033 : Bounds (179083 / 1000000000) (44771 / 250000000) (Real.log (10001791 / 10000000)) := by
  have h := reflection_log_4033_neg
  have he : Real.log (10001791 / 10000000) = -Real.log (10000000 / 10001791) := by
    rw [show ((10001791 / 10000000) : ℝ) = ((10000000 / 10001791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4034_neg : (44779 / 250000000) ≤ -Real.log (9998209 / 10000000) ∧
    -Real.log (9998209 / 10000000) ≤ (179117 / 1000000000) := by
  have h := checkLog_sound (w := (1791 / 19998209)) (n := 12)
    (lo := (44779 / 250000000)) (hi := (179117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998209) = 1/(9998209 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4034 : Bounds (-179117 / 1000000000) (-44779 / 250000000) (Real.log (9998209 / 10000000)) := by
  have h := reflection_log_4034_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4035_neg : (43058113 / 500000000) ≤ -Real.log (1000000 / 1089933) ∧
    -Real.log (1000000 / 1089933) ≤ (86116227 / 1000000000) := by
  have h := checkLog_sound (w := (89933 / 2089933)) (n := 12)
    (lo := (43058113 / 500000000)) (hi := (86116227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089933 / 1000000) = 1/(1000000 / 1089933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4035 : Bounds (43058113 / 500000000) (86116227 / 1000000000) (Real.log (1089933 / 1000000)) := by
  have h := reflection_log_4035_neg
  have he : Real.log (1089933 / 1000000) = -Real.log (1000000 / 1089933) := by
    rw [show ((1089933 / 1000000) : ℝ) = ((1000000 / 1089933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4036_neg : (18847411 / 200000000) ≤ -Real.log (910067 / 1000000) ∧
    -Real.log (910067 / 1000000) ≤ (736227 / 7812500) := by
  have h := checkLog_sound (w := (89933 / 1910067)) (n := 12)
    (lo := (18847411 / 200000000)) (hi := (736227 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910067) = 1/(910067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4036 : Bounds (-736227 / 7812500) (-18847411 / 200000000) (Real.log (910067 / 1000000)) := by
  have h := reflection_log_4036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4037_neg : (86326309 / 1000000000) ≤ -Real.log (500000 / 545081) ∧
    -Real.log (500000 / 545081) ≤ (8632631 / 100000000) := by
  have h := checkLog_sound (w := (45081 / 1045081)) (n := 12)
    (lo := (86326309 / 1000000000)) (hi := (8632631 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545081 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545081 / 500000) = 1/(500000 / 545081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4037 : Bounds (86326309 / 1000000000) (8632631 / 100000000) (Real.log (545081 / 500000)) := by
  have h := reflection_log_4037_neg
  have he : Real.log (545081 / 500000) = -Real.log (500000 / 545081) := by
    rw [show ((545081 / 500000) : ℝ) = ((500000 / 545081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4038_neg : (94488717 / 1000000000) ≤ -Real.log (454919 / 500000) ∧
    -Real.log (454919 / 500000) ≤ (47244359 / 500000000) := by
  have h := checkLog_sound (w := (45081 / 954919)) (n := 12)
    (lo := (94488717 / 1000000000)) (hi := (47244359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454919) = 1/(454919 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4038 : Bounds (-47244359 / 500000000) (-94488717 / 1000000000) (Real.log (454919 / 500000)) := by
  have h := reflection_log_4038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4039_neg : (1020301 / 125000000) ≤ -Real.log (247967703439 / 250000000000) ∧
    -Real.log (247967703439 / 250000000000) ≤ (8162409 / 1000000000) := by
  have h := checkLog_sound (w := (2032296561 / 497967703439)) (n := 12)
    (lo := (1020301 / 125000000)) (hi := (8162409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247967703439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247967703439) = 1/(247967703439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4039 : Bounds (-8162409 / 1000000000) (-1020301 / 125000000) (Real.log (247967703439 / 250000000000)) := by
  have h := reflection_log_4039_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4040_neg : (8120829 / 1000000000) ≤ -Real.log (991912055511 / 1000000000000) ∧
    -Real.log (991912055511 / 1000000000000) ≤ (812083 / 100000000) := by
  have h := checkLog_sound (w := (8087944489 / 1991912055511)) (n := 12)
    (lo := (8120829 / 1000000000)) (hi := (812083 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991912055511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991912055511) = 1/(991912055511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4040 : Bounds (-812083 / 100000000) (-8120829 / 1000000000) (Real.log (991912055511 / 1000000000000)) := by
  have h := reflection_log_4040_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4041_neg : (90176641 / 500000000) ≤ -Real.log (250000000000 / 299410098377) ∧
    -Real.log (250000000000 / 299410098377) ≤ (180353283 / 1000000000) := by
  have h := checkLog_sound (w := (49410098377 / 549410098377)) (n := 12)
    (lo := (90176641 / 500000000)) (hi := (180353283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299410098377 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299410098377 / 250000000000) = 1/(250000000000 / 299410098377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4041 : Bounds (90176641 / 500000000) (180353283 / 1000000000) (Real.log (299410098377 / 250000000000)) := by
  have h := reflection_log_4041_neg
  have he : Real.log (299410098377 / 250000000000) = -Real.log (250000000000 / 299410098377) := by
    rw [show ((299410098377 / 250000000000) : ℝ) = ((250000000000 / 299410098377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4042_neg : (90407513 / 500000000) ≤ -Real.log (500000000000 / 599096762281) ∧
    -Real.log (500000000000 / 599096762281) ≤ (180815027 / 1000000000) := by
  have h := checkLog_sound (w := (99096762281 / 1099096762281)) (n := 12)
    (lo := (90407513 / 500000000)) (hi := (180815027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599096762281 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599096762281 / 500000000000) = 1/(500000000000 / 599096762281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4042 : Bounds (90407513 / 500000000) (180815027 / 1000000000) (Real.log (599096762281 / 500000000000)) := by
  have h := reflection_log_4042_neg
  have he : Real.log (599096762281 / 500000000000) = -Real.log (500000000000 / 599096762281) := by
    rw [show ((599096762281 / 500000000000) : ℝ) = ((500000000000 / 599096762281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4043_neg : (361898791 / 1000000000) ≤ -Real.log (500000000000 / 718026796589) ∧
    -Real.log (500000000000 / 718026796589) ≤ (45237349 / 125000000) := by
  have h := checkLog_sound (w := (218026796589 / 1218026796589)) (n := 12)
    (lo := (361898791 / 1000000000)) (hi := (45237349 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718026796589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718026796589 / 500000000000) = 1/(500000000000 / 718026796589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4043 : Bounds (361898791 / 1000000000) (45237349 / 125000000) (Real.log (718026796589 / 500000000000)) := by
  have h := reflection_log_4043_neg
  have he : Real.log (718026796589 / 500000000000) = -Real.log (500000000000 / 718026796589) := by
    rw [show ((718026796589 / 500000000000) : ℝ) = ((500000000000 / 718026796589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4044_neg : (72421083 / 200000000) ≤ -Real.log (50000000000 / 71817517359) ∧
    -Real.log (50000000000 / 71817517359) ≤ (45263177 / 125000000) := by
  have h := checkLog_sound (w := (21817517359 / 121817517359)) (n := 12)
    (lo := (72421083 / 200000000)) (hi := (45263177 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71817517359 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71817517359 / 50000000000) = 1/(50000000000 / 71817517359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4044 : Bounds (72421083 / 200000000) (45263177 / 125000000) (Real.log (71817517359 / 50000000000)) := by
  have h := reflection_log_4044_neg
  have he : Real.log (71817517359 / 50000000000) = -Real.log (50000000000 / 71817517359) := by
    rw [show ((71817517359 / 50000000000) : ℝ) = ((50000000000 / 71817517359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4045_neg : (82418121 / 500000000) ≤ -Real.log (625 / 737) ∧
    -Real.log (625 / 737) ≤ (164836243 / 1000000000) := by
  have h := checkLog_sound (w := (56 / 681)) (n := 12)
    (lo := (82418121 / 500000000)) (hi := (164836243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737 / 625) = 1/(625 / 737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4045 : Bounds (82418121 / 500000000) (164836243 / 1000000000) (Real.log (737 / 625)) := by
  have h := reflection_log_4045_neg
  have he : Real.log (737 / 625) = -Real.log (625 / 737) := by
    rw [show ((737 / 625) : ℝ) = ((625 / 737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4046_neg : (49368951 / 250000000) ≤ -Real.log (513 / 625) ∧
    -Real.log (513 / 625) ≤ (39495161 / 200000000) := by
  have h := checkLog_sound (w := (56 / 569)) (n := 12)
    (lo := (49368951 / 250000000)) (hi := (39495161 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 513) = 1/(513 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4046 : Bounds (-39495161 / 200000000) (-49368951 / 250000000) (Real.log (513 / 625)) := by
  have h := reflection_log_4046_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4047_neg : (179183 / 1000000000) ≤ -Real.log (78125 / 78139) ∧
    -Real.log (78125 / 78139) ≤ (11199 / 62500000) := by
  have h := checkLog_sound (w := (7 / 78132)) (n := 12)
    (lo := (179183 / 1000000000)) (hi := (11199 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78139 / 78125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78139 / 78125) = 1/(78125 / 78139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4047 : Bounds (179183 / 1000000000) (11199 / 62500000) (Real.log (78139 / 78125)) := by
  have h := reflection_log_4047_neg
  have he : Real.log (78139 / 78125) = -Real.log (78125 / 78139) := by
    rw [show ((78139 / 78125) : ℝ) = ((78125 / 78139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4048_neg : (11201 / 62500000) ≤ -Real.log (78111 / 78125) ∧
    -Real.log (78111 / 78125) ≤ (179217 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 78118)) (n := 12)
    (lo := (11201 / 62500000)) (hi := (179217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78125 / 78111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78125 / 78111) = 1/(78111 / 78125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4048 : Bounds (-179217 / 1000000000) (-11201 / 62500000) (Real.log (78111 / 78125)) := by
  have h := reflection_log_4048_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4049_neg : (86162099 / 1000000000) ≤ -Real.log (1000000 / 1089983) ∧
    -Real.log (1000000 / 1089983) ≤ (861621 / 10000000) := by
  have h := checkLog_sound (w := (89983 / 2089983)) (n := 12)
    (lo := (86162099 / 1000000000)) (hi := (861621 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089983 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089983 / 1000000) = 1/(1000000 / 1089983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4049 : Bounds (86162099 / 1000000000) (861621 / 10000000) (Real.log (1089983 / 1000000)) := by
  have h := reflection_log_4049_neg
  have he : Real.log (1089983 / 1000000) = -Real.log (1000000 / 1089983) := by
    rw [show ((1089983 / 1000000) : ℝ) = ((1000000 / 1089983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4050_neg : (47145999 / 500000000) ≤ -Real.log (910017 / 1000000) ∧
    -Real.log (910017 / 1000000) ≤ (94291999 / 1000000000) := by
  have h := checkLog_sound (w := (89983 / 1910017)) (n := 12)
    (lo := (47145999 / 500000000)) (hi := (94291999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910017) = 1/(910017 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4050 : Bounds (-94291999 / 1000000000) (-47145999 / 500000000) (Real.log (910017 / 1000000)) := by
  have h := reflection_log_4050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4051_neg : (86373089 / 1000000000) ≤ -Real.log (1000000 / 1090213) ∧
    -Real.log (1000000 / 1090213) ≤ (8637309 / 100000000) := by
  have h := checkLog_sound (w := (90213 / 2090213)) (n := 12)
    (lo := (86373089 / 1000000000)) (hi := (8637309 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090213 / 1000000) = 1/(1000000 / 1090213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4051 : Bounds (86373089 / 1000000000) (8637309 / 100000000) (Real.log (1090213 / 1000000)) := by
  have h := reflection_log_4051_neg
  have he : Real.log (1090213 / 1000000) = -Real.log (1000000 / 1090213) := by
    rw [show ((1090213 / 1000000) : ℝ) = ((1000000 / 1090213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4052_neg : (23636193 / 250000000) ≤ -Real.log (909787 / 1000000) ∧
    -Real.log (909787 / 1000000) ≤ (94544773 / 1000000000) := by
  have h := checkLog_sound (w := (90213 / 1909787)) (n := 12)
    (lo := (23636193 / 250000000)) (hi := (94544773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909787) = 1/(909787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4052 : Bounds (-94544773 / 1000000000) (-23636193 / 250000000) (Real.log (909787 / 1000000)) := by
  have h := reflection_log_4052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4053_neg : (4085841 / 500000000) ≤ -Real.log (991861614631 / 1000000000000) ∧
    -Real.log (991861614631 / 1000000000000) ≤ (8171683 / 1000000000) := by
  have h := checkLog_sound (w := (8138385369 / 1991861614631)) (n := 12)
    (lo := (4085841 / 500000000)) (hi := (8171683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991861614631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991861614631) = 1/(991861614631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4053 : Bounds (-8171683 / 1000000000) (-4085841 / 500000000) (Real.log (991861614631 / 1000000000000)) := by
  have h := reflection_log_4053_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4054_neg : (4064949 / 500000000) ≤ -Real.log (991903059711 / 1000000000000) ∧
    -Real.log (991903059711 / 1000000000000) ≤ (8129899 / 1000000000) := by
  have h := checkLog_sound (w := (8096940289 / 1991903059711)) (n := 12)
    (lo := (4064949 / 500000000)) (hi := (8129899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991903059711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991903059711) = 1/(991903059711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4054 : Bounds (-8129899 / 1000000000) (-4064949 / 500000000) (Real.log (991903059711 / 1000000000000)) := by
  have h := reflection_log_4054_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4055_neg : (90227049 / 500000000) ≤ -Real.log (250000000000 / 299440285181) ∧
    -Real.log (250000000000 / 299440285181) ≤ (180454099 / 1000000000) := by
  have h := checkLog_sound (w := (49440285181 / 549440285181)) (n := 12)
    (lo := (90227049 / 500000000)) (hi := (180454099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299440285181 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299440285181 / 250000000000) = 1/(250000000000 / 299440285181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4055 : Bounds (90227049 / 500000000) (180454099 / 1000000000) (Real.log (299440285181 / 250000000000)) := by
  have h := reflection_log_4055_neg
  have he : Real.log (299440285181 / 250000000000) = -Real.log (250000000000 / 299440285181) := by
    rw [show ((299440285181 / 250000000000) : ℝ) = ((250000000000 / 299440285181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4056_neg : (90458931 / 500000000) ≤ -Real.log (500000000000 / 599158374433) ∧
    -Real.log (500000000000 / 599158374433) ≤ (180917863 / 1000000000) := by
  have h := checkLog_sound (w := (99158374433 / 1099158374433)) (n := 12)
    (lo := (90458931 / 500000000)) (hi := (180917863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599158374433 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599158374433 / 500000000000) = 1/(500000000000 / 599158374433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4056 : Bounds (90458931 / 500000000) (180917863 / 1000000000) (Real.log (599158374433 / 500000000000)) := by
  have h := reflection_log_4056_neg
  have he : Real.log (599158374433 / 500000000000) = -Real.log (500000000000 / 599158374433) := by
    rw [show ((599158374433 / 500000000000) : ℝ) = ((500000000000 / 599158374433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4057_neg : (72421083 / 200000000) ≤ -Real.log (500000000000 / 718175173589) ∧
    -Real.log (500000000000 / 718175173589) ≤ (45263177 / 125000000) := by
  have h := checkLog_sound (w := (218175173589 / 1218175173589)) (n := 12)
    (lo := (72421083 / 200000000)) (hi := (45263177 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718175173589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718175173589 / 500000000000) = 1/(500000000000 / 718175173589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4057 : Bounds (72421083 / 200000000) (45263177 / 125000000) (Real.log (718175173589 / 500000000000)) := by
  have h := reflection_log_4057_neg
  have he : Real.log (718175173589 / 500000000000) = -Real.log (500000000000 / 718175173589) := by
    rw [show ((718175173589 / 500000000000) : ℝ) = ((500000000000 / 718175173589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4058_neg : (362312047 / 1000000000) ≤ -Real.log (100000000000 / 143664717349) ∧
    -Real.log (100000000000 / 143664717349) ≤ (22644503 / 62500000) := by
  have h := checkLog_sound (w := (43664717349 / 243664717349)) (n := 12)
    (lo := (362312047 / 1000000000)) (hi := (22644503 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143664717349 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143664717349 / 100000000000) = 1/(100000000000 / 143664717349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4058 : Bounds (362312047 / 1000000000) (22644503 / 62500000) (Real.log (143664717349 / 100000000000)) := by
  have h := reflection_log_4058_neg
  have he : Real.log (143664717349 / 100000000000) = -Real.log (100000000000 / 143664717349) := by
    rw [show ((143664717349 / 100000000000) : ℝ) = ((100000000000 / 143664717349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4059_neg : (82460521 / 500000000) ≤ -Real.log (10000 / 11793) ∧
    -Real.log (10000 / 11793) ≤ (164921043 / 1000000000) := by
  have h := checkLog_sound (w := (1793 / 21793)) (n := 12)
    (lo := (82460521 / 500000000)) (hi := (164921043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11793 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11793 / 10000) = 1/(10000 / 11793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4059 : Bounds (82460521 / 500000000) (164921043 / 1000000000) (Real.log (11793 / 10000)) := by
  have h := reflection_log_4059_neg
  have he : Real.log (11793 / 10000) = -Real.log (10000 / 11793) := by
    rw [show ((11793 / 10000) : ℝ) = ((10000 / 11793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4060_neg : (49399411 / 250000000) ≤ -Real.log (8207 / 10000) ∧
    -Real.log (8207 / 10000) ≤ (39519529 / 200000000) := by
  have h := checkLog_sound (w := (1793 / 18207)) (n := 12)
    (lo := (49399411 / 250000000)) (hi := (39519529 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8207) = 1/(8207 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4060 : Bounds (-39519529 / 200000000) (-49399411 / 250000000) (Real.log (8207 / 10000)) := by
  have h := reflection_log_4060_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4061_neg : (179283 / 1000000000) ≤ -Real.log (10000000 / 10001793) ∧
    -Real.log (10000000 / 10001793) ≤ (44821 / 250000000) := by
  have h := checkLog_sound (w := (1793 / 20001793)) (n := 12)
    (lo := (179283 / 1000000000)) (hi := (44821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001793 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001793 / 10000000) = 1/(10000000 / 10001793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4061 : Bounds (179283 / 1000000000) (44821 / 250000000) (Real.log (10001793 / 10000000)) := by
  have h := reflection_log_4061_neg
  have he : Real.log (10001793 / 10000000) = -Real.log (10000000 / 10001793) := by
    rw [show ((10001793 / 10000000) : ℝ) = ((10000000 / 10001793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4062_neg : (44829 / 250000000) ≤ -Real.log (9998207 / 10000000) ∧
    -Real.log (9998207 / 10000000) ≤ (179317 / 1000000000) := by
  have h := checkLog_sound (w := (1793 / 19998207)) (n := 12)
    (lo := (44829 / 250000000)) (hi := (179317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998207) = 1/(9998207 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4062 : Bounds (-179317 / 1000000000) (-44829 / 250000000) (Real.log (9998207 / 10000000)) := by
  have h := reflection_log_4062_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4063_neg : (10776111 / 125000000) ≤ -Real.log (500000 / 545017) ∧
    -Real.log (500000 / 545017) ≤ (86208889 / 1000000000) := by
  have h := checkLog_sound (w := (45017 / 1045017)) (n := 12)
    (lo := (10776111 / 125000000)) (hi := (86208889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545017 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545017 / 500000) = 1/(500000 / 545017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4063 : Bounds (10776111 / 125000000) (86208889 / 1000000000) (Real.log (545017 / 500000)) := by
  have h := reflection_log_4063_neg
  have he : Real.log (545017 / 500000) = -Real.log (500000 / 545017) := by
    rw [show ((545017 / 500000) : ℝ) = ((500000 / 545017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4064_neg : (47174021 / 500000000) ≤ -Real.log (454983 / 500000) ∧
    -Real.log (454983 / 500000) ≤ (94348043 / 1000000000) := by
  have h := checkLog_sound (w := (45017 / 954983)) (n := 12)
    (lo := (47174021 / 500000000)) (hi := (94348043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454983) = 1/(454983 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4064 : Bounds (-94348043 / 1000000000) (-47174021 / 500000000) (Real.log (454983 / 500000)) := by
  have h := reflection_log_4064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4065_neg : (21604967 / 250000000) ≤ -Real.log (125000 / 136283) ∧
    -Real.log (125000 / 136283) ≤ (86419869 / 1000000000) := by
  have h := checkLog_sound (w := (11283 / 261283)) (n := 12)
    (lo := (21604967 / 250000000)) (hi := (86419869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136283 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136283 / 125000) = 1/(125000 / 136283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4065 : Bounds (21604967 / 250000000) (86419869 / 1000000000) (Real.log (136283 / 125000)) := by
  have h := reflection_log_4065_neg
  have he : Real.log (136283 / 125000) = -Real.log (125000 / 136283) := by
    rw [show ((136283 / 125000) : ℝ) = ((125000 / 136283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4066_neg : (94600831 / 1000000000) ≤ -Real.log (113717 / 125000) ∧
    -Real.log (113717 / 125000) ≤ (739069 / 7812500) := by
  have h := checkLog_sound (w := (11283 / 238717)) (n := 12)
    (lo := (94600831 / 1000000000)) (hi := (739069 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113717) = 1/(113717 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4066 : Bounds (-739069 / 7812500) (-94600831 / 1000000000) (Real.log (113717 / 125000)) := by
  have h := reflection_log_4066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4067_neg : (4090481 / 500000000) ≤ -Real.log (15497693911 / 15625000000) ∧
    -Real.log (15497693911 / 15625000000) ≤ (8180963 / 1000000000) := by
  have h := checkLog_sound (w := (127306089 / 31122693911)) (n := 12)
    (lo := (4090481 / 500000000)) (hi := (8180963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15497693911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15497693911) = 1/(15497693911 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4067 : Bounds (-8180963 / 1000000000) (-4090481 / 500000000) (Real.log (15497693911 / 15625000000)) := by
  have h := reflection_log_4067_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4068_neg : (4069577 / 500000000) ≤ -Real.log (247973469711 / 250000000000) ∧
    -Real.log (247973469711 / 250000000000) ≤ (1627831 / 200000000) := by
  have h := checkLog_sound (w := (2026530289 / 497973469711)) (n := 12)
    (lo := (4069577 / 500000000)) (hi := (1627831 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247973469711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247973469711) = 1/(247973469711 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4068 : Bounds (-1627831 / 200000000) (-4069577 / 500000000) (Real.log (247973469711 / 250000000000)) := by
  have h := reflection_log_4068_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4069_neg : (180556931 / 1000000000) ≤ -Real.log (250000000000 / 299471079139) ∧
    -Real.log (250000000000 / 299471079139) ≤ (45139233 / 250000000) := by
  have h := checkLog_sound (w := (49471079139 / 549471079139)) (n := 12)
    (lo := (180556931 / 1000000000)) (hi := (45139233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299471079139 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299471079139 / 250000000000) = 1/(250000000000 / 299471079139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4069 : Bounds (180556931 / 1000000000) (45139233 / 250000000) (Real.log (299471079139 / 250000000000)) := by
  have h := reflection_log_4069_neg
  have he : Real.log (299471079139 / 250000000000) = -Real.log (250000000000 / 299471079139) := by
    rw [show ((299471079139 / 250000000000) : ℝ) = ((250000000000 / 299471079139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4070_neg : (1810207 / 10000000) ≤ -Real.log (500000000000 / 599219993493) ∧
    -Real.log (500000000000 / 599219993493) ≤ (181020701 / 1000000000) := by
  have h := checkLog_sound (w := (99219993493 / 1099219993493)) (n := 12)
    (lo := (1810207 / 10000000)) (hi := (181020701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599219993493 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599219993493 / 500000000000) = 1/(500000000000 / 599219993493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4070 : Bounds (1810207 / 10000000) (181020701 / 1000000000) (Real.log (599219993493 / 500000000000)) := by
  have h := reflection_log_4070_neg
  have he : Real.log (599219993493 / 500000000000) = -Real.log (500000000000 / 599219993493) := by
    rw [show ((599219993493 / 500000000000) : ℝ) = ((500000000000 / 599219993493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4071_neg : (362312047 / 1000000000) ≤ -Real.log (62500000000 / 89790448343) ∧
    -Real.log (62500000000 / 89790448343) ≤ (22644503 / 62500000) := by
  have h := checkLog_sound (w := (27290448343 / 152290448343)) (n := 12)
    (lo := (362312047 / 1000000000)) (hi := (22644503 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89790448343 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89790448343 / 62500000000) = 1/(62500000000 / 89790448343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4071 : Bounds (362312047 / 1000000000) (22644503 / 62500000) (Real.log (89790448343 / 62500000000)) := by
  have h := reflection_log_4071_neg
  have he : Real.log (89790448343 / 62500000000) = -Real.log (62500000000 / 89790448343) := by
    rw [show ((89790448343 / 62500000000) : ℝ) = ((62500000000 / 89790448343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4072_neg : (181259343 / 500000000) ≤ -Real.log (500000000000 / 718472036067) ∧
    -Real.log (500000000000 / 718472036067) ≤ (362518687 / 1000000000) := by
  have h := checkLog_sound (w := (218472036067 / 1218472036067)) (n := 12)
    (lo := (181259343 / 500000000)) (hi := (362518687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718472036067 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718472036067 / 500000000000) = 1/(500000000000 / 718472036067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4072 : Bounds (181259343 / 500000000) (362518687 / 1000000000) (Real.log (718472036067 / 500000000000)) := by
  have h := reflection_log_4072_neg
  have he : Real.log (718472036067 / 500000000000) = -Real.log (500000000000 / 718472036067) := by
    rw [show ((718472036067 / 500000000000) : ℝ) = ((500000000000 / 718472036067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4073_neg : (82502917 / 500000000) ≤ -Real.log (5000 / 5897) ∧
    -Real.log (5000 / 5897) ≤ (33001167 / 200000000) := by
  have h := checkLog_sound (w := (897 / 10897)) (n := 12)
    (lo := (82502917 / 500000000)) (hi := (33001167 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5897 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5897 / 5000) = 1/(5000 / 5897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4073 : Bounds (82502917 / 500000000) (33001167 / 200000000) (Real.log (5897 / 5000)) := by
  have h := reflection_log_4073_neg
  have he : Real.log (5897 / 5000) = -Real.log (5000 / 5897) := by
    rw [show ((5897 / 5000) : ℝ) = ((5000 / 5897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4074_neg : (98859749 / 500000000) ≤ -Real.log (4103 / 5000) ∧
    -Real.log (4103 / 5000) ≤ (197719499 / 1000000000) := by
  have h := checkLog_sound (w := (897 / 9103)) (n := 12)
    (lo := (98859749 / 500000000)) (hi := (197719499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4103) = 1/(4103 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4074 : Bounds (-197719499 / 1000000000) (-98859749 / 500000000) (Real.log (4103 / 5000)) := by
  have h := reflection_log_4074_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4075_neg : (179383 / 1000000000) ≤ -Real.log (5000000 / 5000897) ∧
    -Real.log (5000000 / 5000897) ≤ (22423 / 125000000) := by
  have h := checkLog_sound (w := (897 / 10000897)) (n := 12)
    (lo := (179383 / 1000000000)) (hi := (22423 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000897 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000897 / 5000000) = 1/(5000000 / 5000897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4075 : Bounds (179383 / 1000000000) (22423 / 125000000) (Real.log (5000897 / 5000000)) := by
  have h := reflection_log_4075_neg
  have he : Real.log (5000897 / 5000000) = -Real.log (5000000 / 5000897) := by
    rw [show ((5000897 / 5000000) : ℝ) = ((5000000 / 5000897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4076_neg : (22427 / 125000000) ≤ -Real.log (4999103 / 5000000) ∧
    -Real.log (4999103 / 5000000) ≤ (179417 / 1000000000) := by
  have h := checkLog_sound (w := (897 / 9999103)) (n := 12)
    (lo := (22427 / 125000000)) (hi := (179417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999103) = 1/(4999103 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4076 : Bounds (-179417 / 1000000000) (-22427 / 125000000) (Real.log (4999103 / 5000000)) := by
  have h := reflection_log_4076_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4077_neg : (43127837 / 500000000) ≤ -Real.log (200000 / 218017) ∧
    -Real.log (200000 / 218017) ≤ (3450227 / 40000000) := by
  have h := checkLog_sound (w := (18017 / 418017)) (n := 12)
    (lo := (43127837 / 500000000)) (hi := (3450227 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218017 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218017 / 200000) = 1/(200000 / 218017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4077 : Bounds (43127837 / 500000000) (3450227 / 40000000) (Real.log (218017 / 200000)) := by
  have h := reflection_log_4077_neg
  have he : Real.log (218017 / 200000) = -Real.log (200000 / 218017) := by
    rw [show ((218017 / 200000) : ℝ) = ((200000 / 218017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4078_neg : (9440409 / 100000000) ≤ -Real.log (181983 / 200000) ∧
    -Real.log (181983 / 200000) ≤ (94404091 / 1000000000) := by
  have h := checkLog_sound (w := (18017 / 381983)) (n := 12)
    (lo := (9440409 / 100000000)) (hi := (94404091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181983) = 1/(181983 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4078 : Bounds (-94404091 / 1000000000) (-9440409 / 100000000) (Real.log (181983 / 200000)) := by
  have h := reflection_log_4078_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4079_neg : (17293329 / 200000000) ≤ -Real.log (200000 / 218063) ∧
    -Real.log (200000 / 218063) ≤ (43233323 / 500000000) := by
  have h := checkLog_sound (w := (18063 / 418063)) (n := 12)
    (lo := (17293329 / 200000000)) (hi := (43233323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218063 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218063 / 200000) = 1/(200000 / 218063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4079 : Bounds (17293329 / 200000000) (43233323 / 500000000) (Real.log (218063 / 200000)) := by
  have h := reflection_log_4079_neg
  have he : Real.log (218063 / 200000) = -Real.log (200000 / 218063) := by
    rw [show ((218063 / 200000) : ℝ) = ((200000 / 218063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4080_neg : (94656893 / 1000000000) ≤ -Real.log (181937 / 200000) ∧
    -Real.log (181937 / 200000) ≤ (47328447 / 500000000) := by
  have h := checkLog_sound (w := (18063 / 381937)) (n := 12)
    (lo := (94656893 / 1000000000)) (hi := (47328447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181937) = 1/(181937 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4080 : Bounds (-47328447 / 500000000) (-94656893 / 1000000000) (Real.log (181937 / 200000)) := by
  have h := reflection_log_4080_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4081_neg : (8190247 / 1000000000) ≤ -Real.log (39673728031 / 40000000000) ∧
    -Real.log (39673728031 / 40000000000) ≤ (1023781 / 125000000) := by
  have h := checkLog_sound (w := (326271969 / 79673728031)) (n := 12)
    (lo := (8190247 / 1000000000)) (hi := (1023781 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39673728031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39673728031) = 1/(39673728031 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4081 : Bounds (-1023781 / 125000000) (-8190247 / 1000000000) (Real.log (39673728031 / 40000000000)) := by
  have h := reflection_log_4081_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4082_neg : (1629683 / 200000000) ≤ -Real.log (39675387711 / 40000000000) ∧
    -Real.log (39675387711 / 40000000000) ≤ (127319 / 15625000) := by
  have h := checkLog_sound (w := (324612289 / 79675387711)) (n := 12)
    (lo := (1629683 / 200000000)) (hi := (127319 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39675387711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39675387711) = 1/(39675387711 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4082 : Bounds (-127319 / 15625000) (-1629683 / 200000000) (Real.log (39675387711 / 40000000000)) := by
  have h := reflection_log_4082_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4083_neg : (36131953 / 200000000) ≤ -Real.log (500000000000 / 599003753097) ∧
    -Real.log (500000000000 / 599003753097) ≤ (90329883 / 500000000) := by
  have h := checkLog_sound (w := (99003753097 / 1099003753097)) (n := 12)
    (lo := (36131953 / 200000000)) (hi := (90329883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599003753097 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599003753097 / 500000000000) = 1/(500000000000 / 599003753097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4083 : Bounds (36131953 / 200000000) (90329883 / 500000000) (Real.log (599003753097 / 500000000000)) := by
  have h := reflection_log_4083_neg
  have he : Real.log (599003753097 / 500000000000) = -Real.log (500000000000 / 599003753097) := by
    rw [show ((599003753097 / 500000000000) : ℝ) = ((500000000000 / 599003753097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4084_neg : (90561769 / 500000000) ≤ -Real.log (250000000000 / 299640809731) ∧
    -Real.log (250000000000 / 299640809731) ≤ (181123539 / 1000000000) := by
  have h := checkLog_sound (w := (49640809731 / 549640809731)) (n := 12)
    (lo := (90561769 / 500000000)) (hi := (181123539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299640809731 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299640809731 / 250000000000) = 1/(250000000000 / 299640809731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4084 : Bounds (90561769 / 500000000) (181123539 / 1000000000) (Real.log (299640809731 / 250000000000)) := by
  have h := reflection_log_4084_neg
  have he : Real.log (299640809731 / 250000000000) = -Real.log (250000000000 / 299640809731) := by
    rw [show ((299640809731 / 250000000000) : ℝ) = ((250000000000 / 299640809731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4085_neg : (181259343 / 500000000) ≤ -Real.log (250000000000 / 359236018033) ∧
    -Real.log (250000000000 / 359236018033) ≤ (362518687 / 1000000000) := by
  have h := checkLog_sound (w := (109236018033 / 609236018033)) (n := 12)
    (lo := (181259343 / 500000000)) (hi := (362518687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359236018033 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359236018033 / 250000000000) = 1/(250000000000 / 359236018033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4085 : Bounds (181259343 / 500000000) (362518687 / 1000000000) (Real.log (359236018033 / 250000000000)) := by
  have h := reflection_log_4085_neg
  have he : Real.log (359236018033 / 250000000000) = -Real.log (250000000000 / 359236018033) := by
    rw [show ((359236018033 / 250000000000) : ℝ) = ((250000000000 / 359236018033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4086_neg : (362725333 / 1000000000) ≤ -Real.log (50000000000 / 71862052157) ∧
    -Real.log (50000000000 / 71862052157) ≤ (181362667 / 500000000) := by
  have h := checkLog_sound (w := (21862052157 / 121862052157)) (n := 12)
    (lo := (362725333 / 1000000000)) (hi := (181362667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71862052157 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71862052157 / 50000000000) = 1/(50000000000 / 71862052157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4086 : Bounds (362725333 / 1000000000) (181362667 / 500000000) (Real.log (71862052157 / 50000000000)) := by
  have h := reflection_log_4086_neg
  have he : Real.log (71862052157 / 50000000000) = -Real.log (50000000000 / 71862052157) := by
    rw [show ((71862052157 / 50000000000) : ℝ) = ((50000000000 / 71862052157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4087_neg : (165090619 / 1000000000) ≤ -Real.log (2000 / 2359) ∧
    -Real.log (2000 / 2359) ≤ (8254531 / 50000000) := by
  have h := checkLog_sound (w := (359 / 4359)) (n := 12)
    (lo := (165090619 / 1000000000)) (hi := (8254531 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2359 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2359 / 2000) = 1/(2000 / 2359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4087 : Bounds (165090619 / 1000000000) (8254531 / 50000000) (Real.log (2359 / 2000)) := by
  have h := reflection_log_4087_neg
  have he : Real.log (2359 / 2000) = -Real.log (2000 / 2359) := by
    rw [show ((2359 / 2000) : ℝ) = ((2000 / 2359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4088_neg : (24730171 / 125000000) ≤ -Real.log (1641 / 2000) ∧
    -Real.log (1641 / 2000) ≤ (197841369 / 1000000000) := by
  have h := checkLog_sound (w := (359 / 3641)) (n := 12)
    (lo := (24730171 / 125000000)) (hi := (197841369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1641) = 1/(1641 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4088 : Bounds (-197841369 / 1000000000) (-24730171 / 125000000) (Real.log (1641 / 2000)) := by
  have h := reflection_log_4088_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4089_neg : (179483 / 1000000000) ≤ -Real.log (2000000 / 2000359) ∧
    -Real.log (2000000 / 2000359) ≤ (44871 / 250000000) := by
  have h := checkLog_sound (w := (359 / 4000359)) (n := 12)
    (lo := (179483 / 1000000000)) (hi := (44871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000359 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000359 / 2000000) = 1/(2000000 / 2000359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4089 : Bounds (179483 / 1000000000) (44871 / 250000000) (Real.log (2000359 / 2000000)) := by
  have h := reflection_log_4089_neg
  have he : Real.log (2000359 / 2000000) = -Real.log (2000000 / 2000359) := by
    rw [show ((2000359 / 2000000) : ℝ) = ((2000000 / 2000359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4090_neg : (44879 / 250000000) ≤ -Real.log (1999641 / 2000000) ∧
    -Real.log (1999641 / 2000000) ≤ (179517 / 1000000000) := by
  have h := checkLog_sound (w := (359 / 3999641)) (n := 12)
    (lo := (44879 / 250000000)) (hi := (179517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999641) = 1/(1999641 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4090 : Bounds (-179517 / 1000000000) (-44879 / 250000000) (Real.log (1999641 / 2000000)) := by
  have h := reflection_log_4090_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4091_neg : (86302459 / 1000000000) ≤ -Real.log (125000 / 136267) ∧
    -Real.log (125000 / 136267) ≤ (4315123 / 50000000) := by
  have h := checkLog_sound (w := (11267 / 261267)) (n := 12)
    (lo := (86302459 / 1000000000)) (hi := (4315123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136267 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136267 / 125000) = 1/(125000 / 136267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4091 : Bounds (86302459 / 1000000000) (4315123 / 50000000) (Real.log (136267 / 125000)) := by
  have h := reflection_log_4091_neg
  have he : Real.log (136267 / 125000) = -Real.log (125000 / 136267) := by
    rw [show ((136267 / 125000) : ℝ) = ((125000 / 136267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4092_neg : (94460141 / 1000000000) ≤ -Real.log (113733 / 125000) ∧
    -Real.log (113733 / 125000) ≤ (47230071 / 500000000) := by
  have h := checkLog_sound (w := (11267 / 238733)) (n := 12)
    (lo := (94460141 / 1000000000)) (hi := (47230071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113733) = 1/(113733 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4092 : Bounds (-47230071 / 500000000) (-94460141 / 1000000000) (Real.log (113733 / 125000)) := by
  have h := reflection_log_4092_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4093_neg : (86513419 / 1000000000) ≤ -Real.log (500000 / 545183) ∧
    -Real.log (500000 / 545183) ≤ (4325671 / 50000000) := by
  have h := checkLog_sound (w := (45183 / 1045183)) (n := 12)
    (lo := (86513419 / 1000000000)) (hi := (4325671 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545183 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545183 / 500000) = 1/(500000 / 545183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4093 : Bounds (86513419 / 1000000000) (4325671 / 50000000) (Real.log (545183 / 500000)) := by
  have h := reflection_log_4093_neg
  have he : Real.log (545183 / 500000) = -Real.log (500000 / 545183) := by
    rw [show ((545183 / 500000) : ℝ) = ((500000 / 545183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4094_neg : (47356479 / 500000000) ≤ -Real.log (454817 / 500000) ∧
    -Real.log (454817 / 500000) ≤ (94712959 / 1000000000) := by
  have h := checkLog_sound (w := (45183 / 954817)) (n := 12)
    (lo := (47356479 / 500000000)) (hi := (94712959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454817) = 1/(454817 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4094 : Bounds (-94712959 / 1000000000) (-47356479 / 500000000) (Real.log (454817 / 500000)) := by
  have h := reflection_log_4094_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4095_neg : (4099769 / 500000000) ≤ -Real.log (247958496511 / 250000000000) ∧
    -Real.log (247958496511 / 250000000000) ≤ (8199539 / 1000000000) := by
  have h := checkLog_sound (w := (2041503489 / 497958496511)) (n := 12)
    (lo := (4099769 / 500000000)) (hi := (8199539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247958496511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247958496511) = 1/(247958496511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4095 : Bounds (-8199539 / 1000000000) (-4099769 / 500000000) (Real.log (247958496511 / 250000000000)) := by
  have h := reflection_log_4095_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
