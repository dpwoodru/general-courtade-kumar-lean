import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7168_neg : (207521 / 1000000000) ≤ -Real.log (399917 / 400000) ∧
    -Real.log (399917 / 400000) ≤ (103761 / 500000000) := by
  have h := checkLog_sound (w := (83 / 799917)) (n := 12)
    (lo := (207521 / 1000000000)) (hi := (103761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399917) = 1/(399917 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7168 : Bounds (-103761 / 500000000) (-207521 / 1000000000) (Real.log (399917 / 400000)) := by
  have h := reflection_log_7168_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7169_neg : (9912743 / 100000000) ≤ -Real.log (1000000 / 1104207) ∧
    -Real.log (1000000 / 1104207) ≤ (99127431 / 1000000000) := by
  have h := checkLog_sound (w := (104207 / 2104207)) (n := 12)
    (lo := (9912743 / 100000000)) (hi := (99127431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1104207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1104207 / 1000000) = 1/(1000000 / 1104207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7169 : Bounds (9912743 / 100000000) (99127431 / 1000000000) (Real.log (1104207 / 1000000)) := by
  have h := reflection_log_7169_neg
  have he : Real.log (1104207 / 1000000) = -Real.log (1000000 / 1104207) := by
    rw [show ((1104207 / 1000000) : ℝ) = ((1000000 / 1104207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7170_neg : (110045919 / 1000000000) ≤ -Real.log (895793 / 1000000) ∧
    -Real.log (895793 / 1000000) ≤ (687787 / 6250000) := by
  have h := checkLog_sound (w := (104207 / 1895793)) (n := 12)
    (lo := (110045919 / 1000000000)) (hi := (687787 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 895793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 895793) = 1/(895793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7170 : Bounds (-687787 / 6250000) (-110045919 / 1000000000) (Real.log (895793 / 1000000)) := by
  have h := reflection_log_7170_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7171_neg : (49772871 / 500000000) ≤ -Real.log (1000000 / 1104669) ∧
    -Real.log (1000000 / 1104669) ≤ (99545743 / 1000000000) := by
  have h := checkLog_sound (w := (104669 / 2104669)) (n := 12)
    (lo := (49772871 / 500000000)) (hi := (99545743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1104669 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1104669 / 1000000) = 1/(1000000 / 1104669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7171 : Bounds (49772871 / 500000000) (99545743 / 1000000000) (Real.log (1104669 / 1000000)) := by
  have h := reflection_log_7171_neg
  have he : Real.log (1104669 / 1000000) = -Real.log (1000000 / 1104669) := by
    rw [show ((1104669 / 1000000) : ℝ) = ((1000000 / 1104669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7172_neg : (27640449 / 250000000) ≤ -Real.log (895331 / 1000000) ∧
    -Real.log (895331 / 1000000) ≤ (110561797 / 1000000000) := by
  have h := checkLog_sound (w := (104669 / 1895331)) (n := 12)
    (lo := (27640449 / 250000000)) (hi := (110561797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 895331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 895331) = 1/(895331 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7172 : Bounds (-110561797 / 1000000000) (-27640449 / 250000000) (Real.log (895331 / 1000000)) := by
  have h := reflection_log_7172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7173_neg : (5508027 / 500000000) ≤ -Real.log (989044400439 / 1000000000000) ∧
    -Real.log (989044400439 / 1000000000000) ≤ (2203211 / 200000000) := by
  have h := checkLog_sound (w := (10955599561 / 1989044400439)) (n := 12)
    (lo := (5508027 / 500000000)) (hi := (2203211 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989044400439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989044400439) = 1/(989044400439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7173 : Bounds (-2203211 / 200000000) (-5508027 / 500000000) (Real.log (989044400439 / 1000000000000)) := by
  have h := reflection_log_7173_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7174_neg : (10918489 / 1000000000) ≤ -Real.log (989140901151 / 1000000000000) ∧
    -Real.log (989140901151 / 1000000000000) ≤ (1091849 / 100000000) := by
  have h := checkLog_sound (w := (10859098849 / 1989140901151)) (n := 12)
    (lo := (10918489 / 1000000000)) (hi := (1091849 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989140901151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989140901151) = 1/(989140901151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7174 : Bounds (-1091849 / 100000000) (-10918489 / 1000000000) (Real.log (989140901151 / 1000000000000)) := by
  have h := reflection_log_7174_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7175_neg : (209173349 / 1000000000) ≤ -Real.log (125000000000 / 154082332637) ∧
    -Real.log (125000000000 / 154082332637) ≤ (4183467 / 20000000) := by
  have h := checkLog_sound (w := (29082332637 / 279082332637)) (n := 12)
    (lo := (209173349 / 1000000000)) (hi := (4183467 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154082332637 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154082332637 / 125000000000) = 1/(125000000000 / 154082332637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7175 : Bounds (209173349 / 1000000000) (4183467 / 20000000) (Real.log (154082332637 / 125000000000)) := by
  have h := reflection_log_7175_neg
  have he : Real.log (154082332637 / 125000000000) = -Real.log (125000000000 / 154082332637) := by
    rw [show ((154082332637 / 125000000000) : ℝ) = ((125000000000 / 154082332637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7176_neg : (210107539 / 1000000000) ≤ -Real.log (500000000000 / 616905367959) ∧
    -Real.log (500000000000 / 616905367959) ≤ (10505377 / 50000000) := by
  have h := checkLog_sound (w := (116905367959 / 1116905367959)) (n := 12)
    (lo := (210107539 / 1000000000)) (hi := (10505377 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((616905367959 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(616905367959 / 500000000000) = 1/(500000000000 / 616905367959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7176 : Bounds (210107539 / 1000000000) (10505377 / 50000000) (Real.log (616905367959 / 500000000000)) := by
  have h := reflection_log_7176_neg
  have he : Real.log (616905367959 / 500000000000) = -Real.log (500000000000 / 616905367959) := by
    rw [show ((616905367959 / 500000000000) : ℝ) = ((500000000000 / 616905367959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7177_neg : (420069999 / 1000000000) ≤ -Real.log (500000000000 / 761034047919) ∧
    -Real.log (500000000000 / 761034047919) ≤ (42007 / 100000) := by
  have h := checkLog_sound (w := (261034047919 / 1261034047919)) (n := 12)
    (lo := (420069999 / 1000000000)) (hi := (42007 / 100000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761034047919 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761034047919 / 500000000000) = 1/(500000000000 / 761034047919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7177 : Bounds (420069999 / 1000000000) (42007 / 100000) (Real.log (761034047919 / 500000000000)) := by
  have h := reflection_log_7177_neg
  have he : Real.log (761034047919 / 500000000000) = -Real.log (500000000000 / 761034047919) := by
    rw [show ((761034047919 / 500000000000) : ℝ) = ((500000000000 / 761034047919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7178_neg : (421114879 / 1000000000) ≤ -Real.log (500000000000 / 761829652997) ∧
    -Real.log (500000000000 / 761829652997) ≤ (164498 / 390625) := by
  have h := checkLog_sound (w := (261829652997 / 1261829652997)) (n := 12)
    (lo := (421114879 / 1000000000)) (hi := (164498 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761829652997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761829652997 / 500000000000) = 1/(500000000000 / 761829652997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7178 : Bounds (421114879 / 1000000000) (164498 / 390625) (Real.log (761829652997 / 500000000000)) := by
  have h := reflection_log_7178_neg
  have he : Real.log (761829652997 / 500000000000) = -Real.log (500000000000 / 761829652997) := by
    rw [show ((761829652997 / 500000000000) : ℝ) = ((500000000000 / 761829652997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7179_neg : (188966099 / 1000000000) ≤ -Real.log (125 / 151) ∧
    -Real.log (125 / 151) ≤ (1889661 / 10000000) := by
  have h := checkLog_sound (w := (13 / 138)) (n := 12)
    (lo := (188966099 / 1000000000)) (hi := (1889661 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151 / 125) = 1/(125 / 151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7179 : Bounds (188966099 / 1000000000) (1889661 / 10000000) (Real.log (151 / 125)) := by
  have h := reflection_log_7179_neg
  have he : Real.log (151 / 125) = -Real.log (125 / 151) := by
    rw [show ((151 / 125) : ℝ) = ((125 / 151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7180_neg : (233193887 / 1000000000) ≤ -Real.log (99 / 125) ∧
    -Real.log (99 / 125) ≤ (7287309 / 31250000) := by
  have h := checkLog_sound (w := (13 / 112)) (n := 12)
    (lo := (233193887 / 1000000000)) (hi := (7287309 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 99) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 99) = 1/(99 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7180 : Bounds (-7287309 / 31250000) (-233193887 / 1000000000) (Real.log (99 / 125)) := by
  have h := reflection_log_7180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7181_neg : (103989 / 500000000) ≤ -Real.log (62500 / 62513) ∧
    -Real.log (62500 / 62513) ≤ (207979 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 125013)) (n := 12)
    (lo := (103989 / 500000000)) (hi := (207979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62513 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62513 / 62500) = 1/(62500 / 62513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7181 : Bounds (103989 / 500000000) (207979 / 1000000000) (Real.log (62513 / 62500)) := by
  have h := reflection_log_7181_neg
  have he : Real.log (62513 / 62500) = -Real.log (62500 / 62513) := by
    rw [show ((62513 / 62500) : ℝ) = ((62500 / 62513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7182_neg : (208021 / 1000000000) ≤ -Real.log (62487 / 62500) ∧
    -Real.log (62487 / 62500) ≤ (104011 / 500000000) := by
  have h := checkLog_sound (w := (13 / 124987)) (n := 12)
    (lo := (208021 / 1000000000)) (hi := (104011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62487) = 1/(62487 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7182 : Bounds (-104011 / 500000000) (-208021 / 1000000000) (Real.log (62487 / 62500)) := by
  have h := reflection_log_7182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7183_neg : (49679169 / 500000000) ≤ -Real.log (500000 / 552231) ∧
    -Real.log (500000 / 552231) ≤ (99358339 / 1000000000) := by
  have h := checkLog_sound (w := (52231 / 1052231)) (n := 12)
    (lo := (49679169 / 500000000)) (hi := (99358339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552231 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552231 / 500000) = 1/(500000 / 552231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7183 : Bounds (49679169 / 500000000) (99358339 / 1000000000) (Real.log (552231 / 500000)) := by
  have h := reflection_log_7183_neg
  have he : Real.log (552231 / 500000) = -Real.log (500000 / 552231) := by
    rw [show ((552231 / 500000) : ℝ) = ((500000 / 552231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7184_neg : (110330623 / 1000000000) ≤ -Real.log (447769 / 500000) ∧
    -Real.log (447769 / 500000) ≤ (430979 / 3906250) := by
  have h := checkLog_sound (w := (52231 / 947769)) (n := 12)
    (lo := (110330623 / 1000000000)) (hi := (430979 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447769) = 1/(447769 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7184 : Bounds (-430979 / 3906250) (-110330623 / 1000000000) (Real.log (447769 / 500000)) := by
  have h := reflection_log_7184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7185_neg : (24944591 / 250000000) ≤ -Real.log (500000 / 552463) ∧
    -Real.log (500000 / 552463) ≤ (19955673 / 200000000) := by
  have h := checkLog_sound (w := (52463 / 1052463)) (n := 12)
    (lo := (24944591 / 250000000)) (hi := (19955673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552463 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552463 / 500000) = 1/(500000 / 552463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7185 : Bounds (24944591 / 250000000) (19955673 / 200000000) (Real.log (552463 / 500000)) := by
  have h := reflection_log_7185_neg
  have he : Real.log (552463 / 500000) = -Real.log (500000 / 552463) := by
    rw [show ((552463 / 500000) : ℝ) = ((500000 / 552463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7186_neg : (55424441 / 500000000) ≤ -Real.log (447537 / 500000) ∧
    -Real.log (447537 / 500000) ≤ (110848883 / 1000000000) := by
  have h := checkLog_sound (w := (52463 / 947537)) (n := 12)
    (lo := (55424441 / 500000000)) (hi := (110848883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447537) = 1/(447537 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7186 : Bounds (-110848883 / 1000000000) (-55424441 / 500000000) (Real.log (447537 / 500000)) := by
  have h := reflection_log_7186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7187_neg : (5535259 / 500000000) ≤ -Real.log (247247633631 / 250000000000) ∧
    -Real.log (247247633631 / 250000000000) ≤ (11070519 / 1000000000) := by
  have h := checkLog_sound (w := (2752366369 / 497247633631)) (n := 12)
    (lo := (5535259 / 500000000)) (hi := (11070519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247247633631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247247633631) = 1/(247247633631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7187 : Bounds (-11070519 / 1000000000) (-5535259 / 500000000) (Real.log (247247633631 / 250000000000)) := by
  have h := reflection_log_7187_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7188_neg : (2194457 / 200000000) ≤ -Real.log (247271922639 / 250000000000) ∧
    -Real.log (247271922639 / 250000000000) ≤ (5486143 / 500000000) := by
  have h := checkLog_sound (w := (2728077361 / 497271922639)) (n := 12)
    (lo := (2194457 / 200000000)) (hi := (5486143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247271922639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247271922639) = 1/(247271922639 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7188 : Bounds (-5486143 / 500000000) (-2194457 / 200000000) (Real.log (247271922639 / 250000000000)) := by
  have h := reflection_log_7188_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7189_neg : (104844481 / 500000000) ≤ -Real.log (500000000000 / 616647199783) ∧
    -Real.log (500000000000 / 616647199783) ≤ (209688963 / 1000000000) := by
  have h := checkLog_sound (w := (116647199783 / 1116647199783)) (n := 12)
    (lo := (104844481 / 500000000)) (hi := (209688963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((616647199783 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(616647199783 / 500000000000) = 1/(500000000000 / 616647199783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7189 : Bounds (104844481 / 500000000) (209688963 / 1000000000) (Real.log (616647199783 / 500000000000)) := by
  have h := reflection_log_7189_neg
  have he : Real.log (616647199783 / 500000000000) = -Real.log (500000000000 / 616647199783) := by
    rw [show ((616647199783 / 500000000000) : ℝ) = ((500000000000 / 616647199783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7190_neg : (105313623 / 500000000) ≤ -Real.log (125000000000 / 154306515439) ∧
    -Real.log (125000000000 / 154306515439) ≤ (210627247 / 1000000000) := by
  have h := checkLog_sound (w := (29306515439 / 279306515439)) (n := 12)
    (lo := (105313623 / 500000000)) (hi := (210627247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154306515439 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154306515439 / 125000000000) = 1/(125000000000 / 154306515439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7190 : Bounds (105313623 / 500000000) (210627247 / 1000000000) (Real.log (154306515439 / 125000000000)) := by
  have h := reflection_log_7190_neg
  have he : Real.log (154306515439 / 125000000000) = -Real.log (125000000000 / 154306515439) := by
    rw [show ((154306515439 / 125000000000) : ℝ) = ((125000000000 / 154306515439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7191_neg : (421114879 / 1000000000) ≤ -Real.log (125000000000 / 190457413249) ∧
    -Real.log (125000000000 / 190457413249) ≤ (164498 / 390625) := by
  have h := checkLog_sound (w := (65457413249 / 315457413249)) (n := 12)
    (lo := (421114879 / 1000000000)) (hi := (164498 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190457413249 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190457413249 / 125000000000) = 1/(125000000000 / 190457413249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7191 : Bounds (421114879 / 1000000000) (164498 / 390625) (Real.log (190457413249 / 125000000000)) := by
  have h := reflection_log_7191_neg
  have he : Real.log (190457413249 / 125000000000) = -Real.log (125000000000 / 190457413249) := by
    rw [show ((190457413249 / 125000000000) : ℝ) = ((125000000000 / 190457413249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7192_neg : (211079993 / 500000000) ≤ -Real.log (500000000000 / 762626262627) ∧
    -Real.log (500000000000 / 762626262627) ≤ (422159987 / 1000000000) := by
  have h := checkLog_sound (w := (262626262627 / 1262626262627)) (n := 12)
    (lo := (211079993 / 500000000)) (hi := (422159987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((762626262627 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(762626262627 / 500000000000) = 1/(500000000000 / 762626262627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7192 : Bounds (211079993 / 500000000) (422159987 / 1000000000) (Real.log (762626262627 / 500000000000)) := by
  have h := reflection_log_7192_neg
  have he : Real.log (762626262627 / 500000000000) = -Real.log (500000000000 / 762626262627) := by
    rw [show ((762626262627 / 500000000000) : ℝ) = ((500000000000 / 762626262627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7193_neg : (189379921 / 1000000000) ≤ -Real.log (2000 / 2417) ∧
    -Real.log (2000 / 2417) ≤ (94689961 / 500000000) := by
  have h := checkLog_sound (w := (417 / 4417)) (n := 12)
    (lo := (189379921 / 1000000000)) (hi := (94689961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2417 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2417 / 2000) = 1/(2000 / 2417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7193 : Bounds (189379921 / 1000000000) (94689961 / 500000000) (Real.log (2417 / 2000)) := by
  have h := reflection_log_7193_neg
  have he : Real.log (2417 / 2000) = -Real.log (2000 / 2417) := by
    rw [show ((2417 / 2000) : ℝ) = ((2000 / 2417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7194_neg : (233825399 / 1000000000) ≤ -Real.log (1583 / 2000) ∧
    -Real.log (1583 / 2000) ≤ (1169127 / 5000000) := by
  have h := checkLog_sound (w := (417 / 3583)) (n := 12)
    (lo := (233825399 / 1000000000)) (hi := (1169127 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1583) = 1/(1583 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7194 : Bounds (-1169127 / 5000000) (-233825399 / 1000000000) (Real.log (1583 / 2000)) := by
  have h := reflection_log_7194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7195_neg : (104239 / 500000000) ≤ -Real.log (2000000 / 2000417) ∧
    -Real.log (2000000 / 2000417) ≤ (208479 / 1000000000) := by
  have h := checkLog_sound (w := (417 / 4000417)) (n := 12)
    (lo := (104239 / 500000000)) (hi := (208479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000417 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000417 / 2000000) = 1/(2000000 / 2000417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7195 : Bounds (104239 / 500000000) (208479 / 1000000000) (Real.log (2000417 / 2000000)) := by
  have h := reflection_log_7195_neg
  have he : Real.log (2000417 / 2000000) = -Real.log (2000000 / 2000417) := by
    rw [show ((2000417 / 2000000) : ℝ) = ((2000000 / 2000417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7196_neg : (208521 / 1000000000) ≤ -Real.log (1999583 / 2000000) ∧
    -Real.log (1999583 / 2000000) ≤ (104261 / 500000000) := by
  have h := checkLog_sound (w := (417 / 3999583)) (n := 12)
    (lo := (208521 / 1000000000)) (hi := (104261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999583) = 1/(1999583 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7196 : Bounds (-104261 / 500000000) (-208521 / 1000000000) (Real.log (1999583 / 2000000)) := by
  have h := reflection_log_7196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7197_neg : (49795049 / 500000000) ≤ -Real.log (500000 / 552359) ∧
    -Real.log (500000 / 552359) ≤ (99590099 / 1000000000) := by
  have h := checkLog_sound (w := (52359 / 1052359)) (n := 12)
    (lo := (49795049 / 500000000)) (hi := (99590099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552359 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552359 / 500000) = 1/(500000 / 552359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7197 : Bounds (49795049 / 500000000) (99590099 / 1000000000) (Real.log (552359 / 500000)) := by
  have h := reflection_log_7197_neg
  have he : Real.log (552359 / 500000) = -Real.log (500000 / 552359) := by
    rw [show ((552359 / 500000) : ℝ) = ((500000 / 552359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7198_neg : (55308263 / 500000000) ≤ -Real.log (447641 / 500000) ∧
    -Real.log (447641 / 500000) ≤ (110616527 / 1000000000) := by
  have h := checkLog_sound (w := (52359 / 947641)) (n := 12)
    (lo := (55308263 / 500000000)) (hi := (110616527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447641) = 1/(447641 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7198 : Bounds (-110616527 / 1000000000) (-55308263 / 500000000) (Real.log (447641 / 500000)) := by
  have h := reflection_log_7198_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7199_neg : (100010027 / 1000000000) ≤ -Real.log (500000 / 552591) ∧
    -Real.log (500000 / 552591) ≤ (25002507 / 250000000) := by
  have h := checkLog_sound (w := (52591 / 1052591)) (n := 12)
    (lo := (100010027 / 1000000000)) (hi := (25002507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552591 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552591 / 500000) = 1/(500000 / 552591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7199 : Bounds (100010027 / 1000000000) (25002507 / 250000000) (Real.log (552591 / 500000)) := by
  have h := reflection_log_7199_neg
  have he : Real.log (552591 / 500000) = -Real.log (500000 / 552591) := by
    rw [show ((552591 / 500000) : ℝ) = ((500000 / 552591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7200_neg : (111134933 / 1000000000) ≤ -Real.log (447409 / 500000) ∧
    -Real.log (447409 / 500000) ≤ (55567467 / 500000000) := by
  have h := checkLog_sound (w := (52591 / 947409)) (n := 12)
    (lo := (111134933 / 1000000000)) (hi := (55567467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447409) = 1/(447409 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7200 : Bounds (-55567467 / 500000000) (-111134933 / 1000000000) (Real.log (447409 / 500000)) := by
  have h := reflection_log_7200_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7201_neg : (5562453 / 500000000) ≤ -Real.log (247234186719 / 250000000000) ∧
    -Real.log (247234186719 / 250000000000) ≤ (11124907 / 1000000000) := by
  have h := checkLog_sound (w := (2765813281 / 497234186719)) (n := 12)
    (lo := (5562453 / 500000000)) (hi := (11124907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247234186719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247234186719) = 1/(247234186719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7201 : Bounds (-11124907 / 1000000000) (-5562453 / 500000000) (Real.log (247234186719 / 250000000000)) := by
  have h := reflection_log_7201_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7202_neg : (11026427 / 1000000000) ≤ -Real.log (247258535119 / 250000000000) ∧
    -Real.log (247258535119 / 250000000000) ≤ (2756607 / 250000000) := by
  have h := checkLog_sound (w := (2741464881 / 497258535119)) (n := 12)
    (lo := (11026427 / 1000000000)) (hi := (2756607 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247258535119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247258535119) = 1/(247258535119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7202 : Bounds (-2756607 / 250000000) (-11026427 / 1000000000) (Real.log (247258535119 / 250000000000)) := by
  have h := reflection_log_7202_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7203_neg : (1681653 / 8000000) ≤ -Real.log (250000000000 / 308483248853) ∧
    -Real.log (250000000000 / 308483248853) ≤ (105103313 / 500000000) := by
  have h := checkLog_sound (w := (58483248853 / 558483248853)) (n := 12)
    (lo := (1681653 / 8000000)) (hi := (105103313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308483248853 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308483248853 / 250000000000) = 1/(250000000000 / 308483248853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7203 : Bounds (1681653 / 8000000) (105103313 / 500000000) (Real.log (308483248853 / 250000000000)) := by
  have h := reflection_log_7203_neg
  have he : Real.log (308483248853 / 250000000000) = -Real.log (250000000000 / 308483248853) := by
    rw [show ((308483248853 / 250000000000) : ℝ) = ((250000000000 / 308483248853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7204_neg : (164957 / 781250) ≤ -Real.log (62500000000 / 77193211357) ∧
    -Real.log (62500000000 / 77193211357) ≤ (211144961 / 1000000000) := by
  have h := checkLog_sound (w := (14693211357 / 139693211357)) (n := 12)
    (lo := (164957 / 781250)) (hi := (211144961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77193211357 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77193211357 / 62500000000) = 1/(62500000000 / 77193211357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7204 : Bounds (164957 / 781250) (211144961 / 1000000000) (Real.log (77193211357 / 62500000000)) := by
  have h := reflection_log_7204_neg
  have he : Real.log (77193211357 / 62500000000) = -Real.log (62500000000 / 77193211357) := by
    rw [show ((77193211357 / 62500000000) : ℝ) = ((62500000000 / 77193211357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7205_neg : (211079993 / 500000000) ≤ -Real.log (250000000000 / 381313131313) ∧
    -Real.log (250000000000 / 381313131313) ≤ (422159987 / 1000000000) := by
  have h := checkLog_sound (w := (131313131313 / 631313131313)) (n := 12)
    (lo := (211079993 / 500000000)) (hi := (422159987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381313131313 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381313131313 / 250000000000) = 1/(250000000000 / 381313131313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7205 : Bounds (211079993 / 500000000) (422159987 / 1000000000) (Real.log (381313131313 / 250000000000)) := by
  have h := reflection_log_7205_neg
  have he : Real.log (381313131313 / 250000000000) = -Real.log (250000000000 / 381313131313) := by
    rw [show ((381313131313 / 250000000000) : ℝ) = ((250000000000 / 381313131313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7206_neg : (10580133 / 25000000) ≤ -Real.log (62500000000 / 95427984839) ∧
    -Real.log (62500000000 / 95427984839) ≤ (423205321 / 1000000000) := by
  have h := checkLog_sound (w := (32927984839 / 157927984839)) (n := 12)
    (lo := (10580133 / 25000000)) (hi := (423205321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95427984839 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95427984839 / 62500000000) = 1/(62500000000 / 95427984839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7206 : Bounds (10580133 / 25000000) (423205321 / 1000000000) (Real.log (95427984839 / 62500000000)) := by
  have h := reflection_log_7206_neg
  have he : Real.log (95427984839 / 62500000000) = -Real.log (62500000000 / 95427984839) := by
    rw [show ((95427984839 / 62500000000) : ℝ) = ((62500000000 / 95427984839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7207_neg : (189793571 / 1000000000) ≤ -Real.log (1000 / 1209) ∧
    -Real.log (1000 / 1209) ≤ (47448393 / 250000000) := by
  have h := checkLog_sound (w := (209 / 2209)) (n := 12)
    (lo := (189793571 / 1000000000)) (hi := (47448393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1209 / 1000) = 1/(1000 / 1209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7207 : Bounds (189793571 / 1000000000) (47448393 / 250000000) (Real.log (1209 / 1000)) := by
  have h := reflection_log_7207_neg
  have he : Real.log (1209 / 1000) = -Real.log (1000 / 1209) := by
    rw [show ((1209 / 1000) : ℝ) = ((1000 / 1209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7208_neg : (234457311 / 1000000000) ≤ -Real.log (791 / 1000) ∧
    -Real.log (791 / 1000) ≤ (7326791 / 31250000) := by
  have h := checkLog_sound (w := (209 / 1791)) (n := 12)
    (lo := (234457311 / 1000000000)) (hi := (7326791 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 791) = 1/(791 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7208 : Bounds (-7326791 / 31250000) (-234457311 / 1000000000) (Real.log (791 / 1000)) := by
  have h := reflection_log_7208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7209_neg : (104489 / 500000000) ≤ -Real.log (1000000 / 1000209) ∧
    -Real.log (1000000 / 1000209) ≤ (208979 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 2000209)) (n := 12)
    (lo := (104489 / 500000000)) (hi := (208979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000209 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000209 / 1000000) = 1/(1000000 / 1000209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7209 : Bounds (104489 / 500000000) (208979 / 1000000000) (Real.log (1000209 / 1000000)) := by
  have h := reflection_log_7209_neg
  have he : Real.log (1000209 / 1000000) = -Real.log (1000000 / 1000209) := by
    rw [show ((1000209 / 1000000) : ℝ) = ((1000000 / 1000209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7210_neg : (209021 / 1000000000) ≤ -Real.log (999791 / 1000000) ∧
    -Real.log (999791 / 1000000) ≤ (104511 / 500000000) := by
  have h := checkLog_sound (w := (209 / 1999791)) (n := 12)
    (lo := (209021 / 1000000000)) (hi := (104511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999791) = 1/(999791 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7210 : Bounds (-104511 / 500000000) (-209021 / 1000000000) (Real.log (999791 / 1000000)) := by
  have h := reflection_log_7210_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7211_neg : (19964361 / 200000000) ≤ -Real.log (500000 / 552487) ∧
    -Real.log (500000 / 552487) ≤ (49910903 / 500000000) := by
  have h := checkLog_sound (w := (52487 / 1052487)) (n := 12)
    (lo := (19964361 / 200000000)) (hi := (49910903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552487 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552487 / 500000) = 1/(500000 / 552487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7211 : Bounds (19964361 / 200000000) (49910903 / 500000000) (Real.log (552487 / 500000)) := by
  have h := reflection_log_7211_neg
  have he : Real.log (552487 / 500000) = -Real.log (500000 / 552487) := by
    rw [show ((552487 / 500000) : ℝ) = ((500000 / 552487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7212_neg : (11090251 / 100000000) ≤ -Real.log (447513 / 500000) ∧
    -Real.log (447513 / 500000) ≤ (110902511 / 1000000000) := by
  have h := checkLog_sound (w := (52487 / 947513)) (n := 12)
    (lo := (11090251 / 100000000)) (hi := (110902511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447513) = 1/(447513 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7212 : Bounds (-110902511 / 1000000000) (-11090251 / 100000000) (Real.log (447513 / 500000)) := by
  have h := reflection_log_7212_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7213_neg : (25060409 / 250000000) ≤ -Real.log (500000 / 552719) ∧
    -Real.log (500000 / 552719) ≤ (100241637 / 1000000000) := by
  have h := checkLog_sound (w := (52719 / 1052719)) (n := 12)
    (lo := (25060409 / 250000000)) (hi := (100241637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552719 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552719 / 500000) = 1/(500000 / 552719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7213 : Bounds (25060409 / 250000000) (100241637 / 1000000000) (Real.log (552719 / 500000)) := by
  have h := reflection_log_7213_neg
  have he : Real.log (552719 / 500000) = -Real.log (500000 / 552719) := by
    rw [show ((552719 / 500000) : ℝ) = ((500000 / 552719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7214_neg : (22284213 / 200000000) ≤ -Real.log (447281 / 500000) ∧
    -Real.log (447281 / 500000) ≤ (55710533 / 500000000) := by
  have h := checkLog_sound (w := (52719 / 947281)) (n := 12)
    (lo := (22284213 / 200000000)) (hi := (55710533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447281) = 1/(447281 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7214 : Bounds (-55710533 / 500000000) (-22284213 / 200000000) (Real.log (447281 / 500000)) := by
  have h := reflection_log_7214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7215_neg : (11179429 / 1000000000) ≤ -Real.log (247220707039 / 250000000000) ∧
    -Real.log (247220707039 / 250000000000) ≤ (1117943 / 100000000) := by
  have h := checkLog_sound (w := (2779292961 / 497220707039)) (n := 12)
    (lo := (11179429 / 1000000000)) (hi := (1117943 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247220707039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247220707039) = 1/(247220707039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7215 : Bounds (-1117943 / 100000000) (-11179429 / 1000000000) (Real.log (247220707039 / 250000000000)) := by
  have h := reflection_log_7215_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7216_neg : (2216141 / 200000000) ≤ -Real.log (247245114831 / 250000000000) ∧
    -Real.log (247245114831 / 250000000000) ≤ (5540353 / 500000000) := by
  have h := checkLog_sound (w := (2754885169 / 497245114831)) (n := 12)
    (lo := (2216141 / 200000000)) (hi := (5540353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247245114831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247245114831) = 1/(247245114831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7216 : Bounds (-5540353 / 500000000) (-2216141 / 200000000) (Real.log (247245114831 / 250000000000)) := by
  have h := reflection_log_7216_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7217_neg : (52681079 / 250000000) ≤ -Real.log (125000000000 / 154321494571) ∧
    -Real.log (125000000000 / 154321494571) ≤ (210724317 / 1000000000) := by
  have h := checkLog_sound (w := (29321494571 / 279321494571)) (n := 12)
    (lo := (52681079 / 250000000)) (hi := (210724317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154321494571 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154321494571 / 125000000000) = 1/(125000000000 / 154321494571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7217 : Bounds (52681079 / 250000000) (210724317 / 1000000000) (Real.log (154321494571 / 125000000000)) := by
  have h := reflection_log_7217_neg
  have he : Real.log (154321494571 / 125000000000) = -Real.log (125000000000 / 154321494571) := by
    rw [show ((154321494571 / 125000000000) : ℝ) = ((125000000000 / 154321494571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7218_neg : (105831351 / 500000000) ≤ -Real.log (100000000000 / 123573100579) ∧
    -Real.log (100000000000 / 123573100579) ≤ (211662703 / 1000000000) := by
  have h := checkLog_sound (w := (23573100579 / 223573100579)) (n := 12)
    (lo := (105831351 / 500000000)) (hi := (211662703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123573100579 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123573100579 / 100000000000) = 1/(100000000000 / 123573100579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7218 : Bounds (105831351 / 500000000) (211662703 / 1000000000) (Real.log (123573100579 / 100000000000)) := by
  have h := reflection_log_7218_neg
  have he : Real.log (123573100579 / 100000000000) = -Real.log (100000000000 / 123573100579) := by
    rw [show ((123573100579 / 100000000000) : ℝ) = ((100000000000 / 123573100579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7219_neg : (10580133 / 25000000) ≤ -Real.log (500000000000 / 763423878711) ∧
    -Real.log (500000000000 / 763423878711) ≤ (423205321 / 1000000000) := by
  have h := checkLog_sound (w := (263423878711 / 1263423878711)) (n := 12)
    (lo := (10580133 / 25000000)) (hi := (423205321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((763423878711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(763423878711 / 500000000000) = 1/(500000000000 / 763423878711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7219 : Bounds (10580133 / 25000000) (423205321 / 1000000000) (Real.log (763423878711 / 500000000000)) := by
  have h := reflection_log_7219_neg
  have he : Real.log (763423878711 / 500000000000) = -Real.log (500000000000 / 763423878711) := by
    rw [show ((763423878711 / 500000000000) : ℝ) = ((500000000000 / 763423878711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7220_neg : (212125441 / 500000000) ≤ -Real.log (500000000000 / 764222503161) ∧
    -Real.log (500000000000 / 764222503161) ≤ (424250883 / 1000000000) := by
  have h := checkLog_sound (w := (264222503161 / 1264222503161)) (n := 12)
    (lo := (212125441 / 500000000)) (hi := (424250883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764222503161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764222503161 / 500000000000) = 1/(500000000000 / 764222503161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7220 : Bounds (212125441 / 500000000) (424250883 / 1000000000) (Real.log (764222503161 / 500000000000)) := by
  have h := reflection_log_7220_neg
  have he : Real.log (764222503161 / 500000000000) = -Real.log (500000000000 / 764222503161) := by
    rw [show ((764222503161 / 500000000000) : ℝ) = ((500000000000 / 764222503161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7221_neg : (190207051 / 1000000000) ≤ -Real.log (2000 / 2419) ∧
    -Real.log (2000 / 2419) ≤ (47551763 / 250000000) := by
  have h := checkLog_sound (w := (419 / 4419)) (n := 12)
    (lo := (190207051 / 1000000000)) (hi := (47551763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2419 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2419 / 2000) = 1/(2000 / 2419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7221 : Bounds (190207051 / 1000000000) (47551763 / 250000000) (Real.log (2419 / 2000)) := by
  have h := reflection_log_7221_neg
  have he : Real.log (2419 / 2000) = -Real.log (2000 / 2419) := by
    rw [show ((2419 / 2000) : ℝ) = ((2000 / 2419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7222_neg : (117544811 / 500000000) ≤ -Real.log (1581 / 2000) ∧
    -Real.log (1581 / 2000) ≤ (235089623 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 3581)) (n := 12)
    (lo := (117544811 / 500000000)) (hi := (235089623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1581) = 1/(1581 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7222 : Bounds (-235089623 / 1000000000) (-117544811 / 500000000) (Real.log (1581 / 2000)) := by
  have h := reflection_log_7222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7223_neg : (104739 / 500000000) ≤ -Real.log (2000000 / 2000419) ∧
    -Real.log (2000000 / 2000419) ≤ (209479 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 4000419)) (n := 12)
    (lo := (104739 / 500000000)) (hi := (209479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000419 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000419 / 2000000) = 1/(2000000 / 2000419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7223 : Bounds (104739 / 500000000) (209479 / 1000000000) (Real.log (2000419 / 2000000)) := by
  have h := reflection_log_7223_neg
  have he : Real.log (2000419 / 2000000) = -Real.log (2000000 / 2000419) := by
    rw [show ((2000419 / 2000000) : ℝ) = ((2000000 / 2000419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7224_neg : (209521 / 1000000000) ≤ -Real.log (1999581 / 2000000) ∧
    -Real.log (1999581 / 2000000) ≤ (104761 / 500000000) := by
  have h := checkLog_sound (w := (419 / 3999581)) (n := 12)
    (lo := (209521 / 1000000000)) (hi := (104761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999581) = 1/(1999581 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7224 : Bounds (-104761 / 500000000) (-209521 / 1000000000) (Real.log (1999581 / 2000000)) := by
  have h := reflection_log_7224_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7225_neg : (50026729 / 500000000) ≤ -Real.log (100000 / 110523) ∧
    -Real.log (100000 / 110523) ≤ (100053459 / 1000000000) := by
  have h := checkLog_sound (w := (10523 / 210523)) (n := 12)
    (lo := (50026729 / 500000000)) (hi := (100053459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110523 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(110523 / 100000) = 1/(100000 / 110523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7225 : Bounds (50026729 / 500000000) (100053459 / 1000000000) (Real.log (110523 / 100000)) := by
  have h := reflection_log_7225_neg
  have he : Real.log (110523 / 100000) = -Real.log (100000 / 110523) := by
    rw [show ((110523 / 100000) : ℝ) = ((100000 / 110523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7226_neg : (3474643 / 31250000) ≤ -Real.log (89477 / 100000) ∧
    -Real.log (89477 / 100000) ≤ (111188577 / 1000000000) := by
  have h := checkLog_sound (w := (10523 / 189477)) (n := 12)
    (lo := (3474643 / 31250000)) (hi := (111188577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 89477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 89477) = 1/(89477 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7226 : Bounds (-111188577 / 1000000000) (-3474643 / 31250000) (Real.log (89477 / 100000)) := by
  have h := reflection_log_7226_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7227_neg : (12559149 / 125000000) ≤ -Real.log (500000 / 552847) ∧
    -Real.log (500000 / 552847) ≤ (100473193 / 1000000000) := by
  have h := checkLog_sound (w := (52847 / 1052847)) (n := 12)
    (lo := (12559149 / 125000000)) (hi := (100473193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552847 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552847 / 500000) = 1/(500000 / 552847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7227 : Bounds (12559149 / 125000000) (100473193 / 1000000000) (Real.log (552847 / 500000)) := by
  have h := reflection_log_7227_neg
  have he : Real.log (552847 / 500000) = -Real.log (500000 / 552847) := by
    rw [show ((552847 / 500000) : ℝ) = ((500000 / 552847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7228_neg : (1396341 / 12500000) ≤ -Real.log (447153 / 500000) ∧
    -Real.log (447153 / 500000) ≤ (111707281 / 1000000000) := by
  have h := checkLog_sound (w := (52847 / 947153)) (n := 12)
    (lo := (1396341 / 12500000)) (hi := (111707281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447153) = 1/(447153 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7228 : Bounds (-111707281 / 1000000000) (-1396341 / 12500000) (Real.log (447153 / 500000)) := by
  have h := reflection_log_7228_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7229_neg : (1404261 / 125000000) ≤ -Real.log (247207194591 / 250000000000) ∧
    -Real.log (247207194591 / 250000000000) ≤ (11234089 / 1000000000) := by
  have h := checkLog_sound (w := (2792805409 / 497207194591)) (n := 12)
    (lo := (1404261 / 125000000)) (hi := (11234089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247207194591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247207194591) = 1/(247207194591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7229 : Bounds (-11234089 / 1000000000) (-1404261 / 125000000) (Real.log (247207194591 / 250000000000)) := by
  have h := reflection_log_7229_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7230_neg : (5567559 / 500000000) ≤ -Real.log (9889266471 / 10000000000) ∧
    -Real.log (9889266471 / 10000000000) ≤ (11135119 / 1000000000) := by
  have h := checkLog_sound (w := (110733529 / 19889266471)) (n := 12)
    (lo := (5567559 / 500000000)) (hi := (11135119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9889266471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9889266471) = 1/(9889266471 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7230 : Bounds (-11135119 / 1000000000) (-5567559 / 500000000) (Real.log (9889266471 / 10000000000)) := by
  have h := reflection_log_7230_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7231_neg : (42248407 / 200000000) ≤ -Real.log (500000000000 / 617605641673) ∧
    -Real.log (500000000000 / 617605641673) ≤ (52810509 / 250000000) := by
  have h := checkLog_sound (w := (117605641673 / 1117605641673)) (n := 12)
    (lo := (42248407 / 200000000)) (hi := (52810509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((617605641673 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(617605641673 / 500000000000) = 1/(500000000000 / 617605641673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7231 : Bounds (42248407 / 200000000) (52810509 / 250000000) (Real.log (617605641673 / 500000000000)) := by
  have h := reflection_log_7231_neg
  have he : Real.log (617605641673 / 500000000000) = -Real.log (500000000000 / 617605641673) := by
    rw [show ((617605641673 / 500000000000) : ℝ) = ((500000000000 / 617605641673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
