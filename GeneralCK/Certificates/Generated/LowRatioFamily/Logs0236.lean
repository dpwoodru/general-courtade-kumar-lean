import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15104_neg : (5352461 / 7812500) ≤ -Real.log (125 / 248) ∧
    -Real.log (125 / 248) ≤ (685115009 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 373)) (n := 12)
    (lo := (5352461 / 7812500)) (hi := (685115009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248 / 125) = 1/(125 / 248) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15104 : Bounds (5352461 / 7812500) (685115009 / 1000000000) (Real.log (248 / 125)) := by
  have h := reflection_log_15104_neg
  have he : Real.log (248 / 125) = -Real.log (125 / 248) := by
    rw [show ((248 / 125) : ℝ) = ((125 / 248) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15105_neg : (4135166553 / 1000000000) ≤ -Real.log (2 / 125) ∧
    -Real.log (2 / 125) ≤ (4135166559 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 64) = 1/(2 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15105 : Bounds (-4135166559 / 1000000000) (-4135166553 / 1000000000) (Real.log (2 / 125)) := by
  have h := reflection_log_15105_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15106_neg : (245879 / 250000000) ≤ -Real.log (125000 / 125123) ∧
    -Real.log (125000 / 125123) ≤ (983517 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 250123)) (n := 12)
    (lo := (245879 / 250000000)) (hi := (983517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125123 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125123 / 125000) = 1/(125000 / 125123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15106 : Bounds (245879 / 250000000) (983517 / 1000000000) (Real.log (125123 / 125000)) := by
  have h := reflection_log_15106_neg
  have he : Real.log (125123 / 125000) = -Real.log (125000 / 125123) := by
    rw [show ((125123 / 125000) : ℝ) = ((125000 / 125123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15107_neg : (246121 / 250000000) ≤ -Real.log (124877 / 125000) ∧
    -Real.log (124877 / 125000) ≤ (196897 / 200000000) := by
  have h := checkLog_sound (w := (123 / 249877)) (n := 12)
    (lo := (246121 / 250000000)) (hi := (196897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124877) = 1/(124877 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15107 : Bounds (-196897 / 200000000) (-246121 / 250000000) (Real.log (124877 / 125000)) := by
  have h := reflection_log_15107_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15108_neg : (48971863 / 100000000) ≤ -Real.log (1000000 / 1631857) ∧
    -Real.log (1000000 / 1631857) ≤ (489718631 / 1000000000) := by
  have h := checkLog_sound (w := (631857 / 2631857)) (n := 12)
    (lo := (48971863 / 100000000)) (hi := (489718631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1631857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1631857 / 1000000) = 1/(1000000 / 1631857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15108 : Bounds (48971863 / 100000000) (489718631 / 1000000000) (Real.log (1631857 / 1000000)) := by
  have h := reflection_log_15108_neg
  have he : Real.log (1631857 / 1000000) = -Real.log (1000000 / 1631857) := by
    rw [show ((1631857 / 1000000) : ℝ) = ((1000000 / 1631857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15109_neg : (249820957 / 250000000) ≤ -Real.log (368143 / 1000000) ∧
    -Real.log (368143 / 1000000) ≤ (99928383 / 100000000) := by
  have h := checkLog_sound (w := (131857 / 868143)) (n := 12)
    (lo := (38267081 / 125000000)) (hi := (306136649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 368143) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 368143) = 1/(368143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15109 : Bounds (-99928383 / 100000000) (-249820957 / 250000000) (Real.log (368143 / 1000000)) := by
  have h := reflection_log_15109_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15110_neg : (122734033 / 250000000) ≤ -Real.log (200000 / 326769) ∧
    -Real.log (200000 / 326769) ≤ (490936133 / 1000000000) := by
  have h := checkLog_sound (w := (126769 / 526769)) (n := 12)
    (lo := (122734033 / 250000000)) (hi := (490936133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326769 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326769 / 200000) = 1/(200000 / 326769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15110 : Bounds (122734033 / 250000000) (490936133 / 1000000000) (Real.log (326769 / 200000)) := by
  have h := reflection_log_15110_neg
  have he : Real.log (326769 / 200000) = -Real.log (200000 / 326769) := by
    rw [show ((326769 / 200000) : ℝ) = ((200000 / 326769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15111_neg : (1004698537 / 1000000000) ≤ -Real.log (73231 / 200000) ∧
    -Real.log (73231 / 200000) ≤ (1004698539 / 1000000000) := by
  have h := checkLog_sound (w := (26769 / 173231)) (n := 12)
    (lo := (311551357 / 1000000000)) (hi := (155775679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 73231) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 73231) = 1/(73231 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15111 : Bounds (-1004698539 / 1000000000) (-1004698537 / 1000000000) (Real.log (73231 / 200000)) := by
  have h := reflection_log_15111_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15112_neg : (102752481 / 200000000) ≤ -Real.log (23929620639 / 40000000000) ∧
    -Real.log (23929620639 / 40000000000) ≤ (256881203 / 500000000) := by
  have h := checkLog_sound (w := (16070379361 / 63929620639)) (n := 12)
    (lo := (102752481 / 200000000)) (hi := (256881203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 23929620639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 23929620639) = 1/(23929620639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15112 : Bounds (-256881203 / 500000000) (-102752481 / 200000000) (Real.log (23929620639 / 40000000000)) := by
  have h := reflection_log_15112_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15113_neg : (509565199 / 1000000000) ≤ -Real.log (600756731551 / 1000000000000) ∧
    -Real.log (600756731551 / 1000000000000) ≤ (1273913 / 2500000) := by
  have h := checkLog_sound (w := (399243268449 / 1600756731551)) (n := 12)
    (lo := (509565199 / 1000000000)) (hi := (1273913 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 600756731551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 600756731551) = 1/(600756731551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15113 : Bounds (-1273913 / 2500000) (-509565199 / 1000000000) (Real.log (600756731551 / 1000000000000)) := by
  have h := reflection_log_15113_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15114_neg : (744501229 / 500000000) ≤ -Real.log (500000000000 / 2216335771697) ∧
    -Real.log (500000000000 / 2216335771697) ≤ (1489002461 / 1000000000) := by
  have h := checkLog_sound (w := (216335771697 / 4216335771697)) (n := 12)
    (lo := (51354049 / 500000000)) (hi := (102708099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2216335771697 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2216335771697 / 2000000000000) = 1/(500000000000 / 2216335771697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15114 : Bounds (744501229 / 500000000) (1489002461 / 1000000000) (Real.log (2216335771697 / 500000000000)) := by
  have h := reflection_log_15114_neg
  have he : Real.log (2216335771697 / 500000000000) = -Real.log (500000000000 / 2216335771697) := by
    rw [show ((2216335771697 / 500000000000) : ℝ) = ((500000000000 / 2216335771697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15115_neg : (1495634669 / 1000000000) ≤ -Real.log (500000000000 / 2231083830619) ∧
    -Real.log (500000000000 / 2231083830619) ≤ (93477167 / 62500000) := by
  have h := checkLog_sound (w := (231083830619 / 4231083830619)) (n := 12)
    (lo := (109340309 / 1000000000)) (hi := (10934031 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2231083830619 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2231083830619 / 2000000000000) = 1/(500000000000 / 2231083830619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15115 : Bounds (1495634669 / 1000000000) (93477167 / 62500000) (Real.log (2231083830619 / 500000000000)) := by
  have h := reflection_log_15115_neg
  have he : Real.log (2231083830619 / 500000000000) = -Real.log (500000000000 / 2231083830619) := by
    rw [show ((2231083830619 / 500000000000) : ℝ) = ((500000000000 / 2231083830619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15116_neg : (4759152781 / 1000000000) ≤ -Real.log (125000000000 / 14580882352941) ∧
    -Real.log (125000000000 / 14580882352941) ≤ (1189788197 / 250000000) := by
  have h := checkLog_sound (w := (6580882352941 / 22580882352941)) (n := 12)
    (lo := (600269701 / 1000000000)) (hi := (300134851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14580882352941 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(14580882352941 / 8000000000000) = 1/(125000000000 / 14580882352941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15116 : Bounds (4759152781 / 1000000000) (1189788197 / 250000000) (Real.log (14580882352941 / 125000000000)) := by
  have h := reflection_log_15116_neg
  have he : Real.log (14580882352941 / 125000000000) = -Real.log (125000000000 / 14580882352941) := by
    rw [show ((14580882352941 / 125000000000) : ℝ) = ((125000000000 / 14580882352941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15117_neg : (2410140781 / 500000000) ≤ -Real.log (1 / 124) ∧
    -Real.log (1 / 124) ≤ (4820281569 / 1000000000) := by
  have h := checkLog_sound (w := (15 / 47)) (n := 12)
    (lo := (330699241 / 500000000)) (hi := (661398483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31 / 16) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(31 / 16) = 1/(1 / 124) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15117 : Bounds (2410140781 / 500000000) (4820281569 / 1000000000) (Real.log (124 / 1)) := by
  have h := reflection_log_15117_neg
  have he : Real.log (124 / 1) = -Real.log (1 / 124) := by
    rw [show ((124 / 1) : ℝ) = ((1 / 124) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15118_neg : (342809457 / 500000000) ≤ -Real.log (200 / 397) ∧
    -Real.log (200 / 397) ≤ (137123783 / 200000000) := by
  have h := checkLog_sound (w := (197 / 597)) (n := 12)
    (lo := (342809457 / 500000000)) (hi := (137123783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397 / 200) = 1/(200 / 397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15118 : Bounds (342809457 / 500000000) (137123783 / 200000000) (Real.log (397 / 200)) := by
  have h := reflection_log_15118_neg
  have he : Real.log (397 / 200) = -Real.log (200 / 397) := by
    rw [show ((397 / 200) : ℝ) = ((200 / 397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15119_neg : (2099852537 / 500000000) ≤ -Real.log (3 / 200) ∧
    -Real.log (3 / 200) ≤ (4199705081 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 49)) (n := 12)
    (lo := (20410997 / 500000000)) (hi := (8164399 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 24) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(25 / 24) = 1/(3 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15119 : Bounds (-4199705081 / 1000000000) (-2099852537 / 500000000) (Real.log (3 / 200)) := by
  have h := reflection_log_15119_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15120_neg : (196903 / 200000000) ≤ -Real.log (200000 / 200197) ∧
    -Real.log (200000 / 200197) ≤ (246129 / 250000000) := by
  have h := checkLog_sound (w := (197 / 400197)) (n := 12)
    (lo := (196903 / 200000000)) (hi := (246129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200197 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200197 / 200000) = 1/(200000 / 200197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15120 : Bounds (196903 / 200000000) (246129 / 250000000) (Real.log (200197 / 200000)) := by
  have h := reflection_log_15120_neg
  have he : Real.log (200197 / 200000) = -Real.log (200000 / 200197) := by
    rw [show ((200197 / 200000) : ℝ) = ((200000 / 200197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15121_neg : (197097 / 200000000) ≤ -Real.log (199803 / 200000) ∧
    -Real.log (199803 / 200000) ≤ (492743 / 500000000) := by
  have h := checkLog_sound (w := (197 / 399803)) (n := 12)
    (lo := (197097 / 200000000)) (hi := (492743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199803) = 1/(199803 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15121 : Bounds (-492743 / 500000000) (-197097 / 200000000) (Real.log (199803 / 200000)) := by
  have h := reflection_log_15121_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15122_neg : (245273089 / 500000000) ≤ -Real.log (125000 / 204151) ∧
    -Real.log (125000 / 204151) ≤ (490546179 / 1000000000) := by
  have h := checkLog_sound (w := (79151 / 329151)) (n := 12)
    (lo := (245273089 / 500000000)) (hi := (490546179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204151 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204151 / 125000) = 1/(125000 / 204151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15122 : Bounds (245273089 / 500000000) (490546179 / 1000000000) (Real.log (204151 / 125000)) := by
  have h := reflection_log_15122_neg
  have he : Real.log (204151 / 125000) = -Real.log (125000 / 204151) := by
    rw [show ((204151 / 125000) : ℝ) = ((125000 / 204151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15123_neg : (250740087 / 250000000) ≤ -Real.log (45849 / 125000) ∧
    -Real.log (45849 / 125000) ≤ (20059207 / 20000000) := by
  have h := checkLog_sound (w := (16651 / 108349)) (n := 12)
    (lo := (19363323 / 62500000)) (hi := (309813169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45849) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 45849) = 1/(45849 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15123 : Bounds (-20059207 / 20000000) (-250740087 / 250000000) (Real.log (45849 / 125000)) := by
  have h := reflection_log_15123_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15124_neg : (122942809 / 250000000) ≤ -Real.log (100000 / 163521) ∧
    -Real.log (100000 / 163521) ≤ (491771237 / 1000000000) := by
  have h := checkLog_sound (w := (63521 / 263521)) (n := 12)
    (lo := (122942809 / 250000000)) (hi := (491771237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163521 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163521 / 100000) = 1/(100000 / 163521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15124 : Bounds (122942809 / 250000000) (491771237 / 1000000000) (Real.log (163521 / 100000)) := by
  have h := reflection_log_15124_neg
  have he : Real.log (163521 / 100000) = -Real.log (100000 / 163521) := by
    rw [show ((163521 / 100000) : ℝ) = ((100000 / 163521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15125_neg : (126054179 / 125000000) ≤ -Real.log (36479 / 100000) ∧
    -Real.log (36479 / 100000) ≤ (504216717 / 500000000) := by
  have h := checkLog_sound (w := (13521 / 86479)) (n := 12)
    (lo := (78821563 / 250000000)) (hi := (315286253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36479) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 36479) = 1/(36479 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15125 : Bounds (-504216717 / 500000000) (-126054179 / 125000000) (Real.log (36479 / 100000)) := by
  have h := reflection_log_15125_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15126_neg : (129165549 / 250000000) ≤ -Real.log (5965082559 / 10000000000) ∧
    -Real.log (5965082559 / 10000000000) ≤ (516662197 / 1000000000) := by
  have h := checkLog_sound (w := (4034917441 / 15965082559)) (n := 12)
    (lo := (129165549 / 250000000)) (hi := (516662197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5965082559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5965082559) = 1/(5965082559 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15126 : Bounds (-516662197 / 1000000000) (-129165549 / 250000000) (Real.log (5965082559 / 10000000000)) := by
  have h := reflection_log_15126_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15127_neg : (51241417 / 100000000) ≤ -Real.log (9360119199 / 15625000000) ∧
    -Real.log (9360119199 / 15625000000) ≤ (512414171 / 1000000000) := by
  have h := checkLog_sound (w := (6264880801 / 24985119199)) (n := 12)
    (lo := (51241417 / 100000000)) (hi := (512414171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 9360119199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 9360119199) = 1/(9360119199 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15127 : Bounds (-512414171 / 1000000000) (-51241417 / 100000000) (Real.log (9360119199 / 15625000000)) := by
  have h := reflection_log_15127_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15128_neg : (746753263 / 500000000) ≤ -Real.log (125000000000 / 556585203603) ∧
    -Real.log (125000000000 / 556585203603) ≤ (1493506529 / 1000000000) := by
  have h := checkLog_sound (w := (56585203603 / 1056585203603)) (n := 12)
    (lo := (53606083 / 500000000)) (hi := (107212167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556585203603 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(556585203603 / 500000000000) = 1/(125000000000 / 556585203603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15128 : Bounds (746753263 / 500000000) (1493506529 / 1000000000) (Real.log (556585203603 / 125000000000)) := by
  have h := reflection_log_15128_neg
  have he : Real.log (556585203603 / 125000000000) = -Real.log (125000000000 / 556585203603) := by
    rw [show ((556585203603 / 125000000000) : ℝ) = ((125000000000 / 556585203603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15129_neg : (375051167 / 250000000) ≤ -Real.log (500000000000 / 2241303215549) ∧
    -Real.log (500000000000 / 2241303215549) ≤ (1500204671 / 1000000000) := by
  have h := checkLog_sound (w := (241303215549 / 4241303215549)) (n := 12)
    (lo := (28477577 / 250000000)) (hi := (113910309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2241303215549 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2241303215549 / 2000000000000) = 1/(500000000000 / 2241303215549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15129 : Bounds (375051167 / 250000000) (1500204671 / 1000000000) (Real.log (2241303215549 / 500000000000)) := by
  have h := reflection_log_15129_neg
  have he : Real.log (2241303215549 / 500000000000) = -Real.log (500000000000 / 2241303215549) := by
    rw [show ((2241303215549 / 500000000000) : ℝ) = ((500000000000 / 2241303215549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15130_neg : (1221330997 / 250000000) ≤ -Real.log (500000000000 / 66166666666667) ∧
    -Real.log (500000000000 / 66166666666667) ≤ (1221330999 / 250000000) := by
  have h := checkLog_sound (w := (2166666666667 / 130166666666667)) (n := 12)
    (lo := (1040429 / 31250000)) (hi := (33293729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66166666666667 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(66166666666667 / 64000000000000) = 1/(500000000000 / 66166666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15130 : Bounds (1221330997 / 250000000) (1221330999 / 250000000) (Real.log (66166666666667 / 500000000000)) := by
  have h := reflection_log_15130_neg
  have he : Real.log (66166666666667 / 500000000000) = -Real.log (500000000000 / 66166666666667) := by
    rw [show ((66166666666667 / 500000000000) : ℝ) = ((500000000000 / 66166666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15131_neg : (137224513 / 200000000) ≤ -Real.log (500 / 993) ∧
    -Real.log (500 / 993) ≤ (343061283 / 500000000) := by
  have h := checkLog_sound (w := (493 / 1493)) (n := 12)
    (lo := (137224513 / 200000000)) (hi := (343061283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((993 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(993 / 500) = 1/(500 / 993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15131 : Bounds (137224513 / 200000000) (343061283 / 500000000) (Real.log (993 / 500)) := by
  have h := reflection_log_15131_neg
  have he : Real.log (993 / 500) = -Real.log (500 / 993) := by
    rw [show ((993 / 500) : ℝ) = ((500 / 993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15132_neg : (2134348973 / 500000000) ≤ -Real.log (7 / 500) ∧
    -Real.log (7 / 500) ≤ (4268697953 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 237)) (n := 12)
    (lo := (54907433 / 500000000)) (hi := (109814867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 112) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(125 / 112) = 1/(7 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15132 : Bounds (-4268697953 / 1000000000) (-2134348973 / 500000000) (Real.log (7 / 500)) := by
  have h := reflection_log_15132_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15133_neg : (492757 / 500000000) ≤ -Real.log (500000 / 500493) ∧
    -Real.log (500000 / 500493) ≤ (197103 / 200000000) := by
  have h := checkLog_sound (w := (493 / 1000493)) (n := 12)
    (lo := (492757 / 500000000)) (hi := (197103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500493 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500493 / 500000) = 1/(500000 / 500493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15133 : Bounds (492757 / 500000000) (197103 / 200000000) (Real.log (500493 / 500000)) := by
  have h := reflection_log_15133_neg
  have he : Real.log (500493 / 500000) = -Real.log (500000 / 500493) := by
    rw [show ((500493 / 500000) : ℝ) = ((500000 / 500493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15134_neg : (493243 / 500000000) ≤ -Real.log (499507 / 500000) ∧
    -Real.log (499507 / 500000) ≤ (986487 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 999507)) (n := 12)
    (lo := (493243 / 500000000)) (hi := (986487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499507) = 1/(499507 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15134 : Bounds (-986487 / 1000000000) (-493243 / 500000000) (Real.log (499507 / 500000)) := by
  have h := reflection_log_15134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15135_neg : (491382219 / 1000000000) ≤ -Real.log (500000 / 817287) ∧
    -Real.log (500000 / 817287) ≤ (24569111 / 50000000) := by
  have h := checkLog_sound (w := (317287 / 1317287)) (n := 12)
    (lo := (491382219 / 1000000000)) (hi := (24569111 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((817287 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(817287 / 500000) = 1/(500000 / 817287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15135 : Bounds (491382219 / 1000000000) (24569111 / 50000000) (Real.log (817287 / 500000)) := by
  have h := reflection_log_15135_neg
  have he : Real.log (817287 / 500000) = -Real.log (500000 / 817287) := by
    rw [show ((817287 / 500000) : ℝ) = ((500000 / 817287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15136_neg : (503345741 / 500000000) ≤ -Real.log (182713 / 500000) ∧
    -Real.log (182713 / 500000) ≤ (251672871 / 250000000) := by
  have h := checkLog_sound (w := (67287 / 432713)) (n := 12)
    (lo := (156772151 / 500000000)) (hi := (313544303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 182713) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 182713) = 1/(182713 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15136 : Bounds (-251672871 / 250000000) (-503345741 / 500000000) (Real.log (182713 / 500000)) := by
  have h := reflection_log_15136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15137_neg : (61576851 / 125000000) ≤ -Real.log (100000 / 163659) ∧
    -Real.log (100000 / 163659) ≤ (492614809 / 1000000000) := by
  have h := checkLog_sound (w := (63659 / 263659)) (n := 12)
    (lo := (61576851 / 125000000)) (hi := (492614809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163659 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163659 / 100000) = 1/(100000 / 163659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15137 : Bounds (61576851 / 125000000) (492614809 / 1000000000) (Real.log (163659 / 100000)) := by
  have h := reflection_log_15137_neg
  have he : Real.log (163659 / 100000) = -Real.log (100000 / 163659) := by
    rw [show ((163659 / 100000) : ℝ) = ((100000 / 163659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15138_neg : (253055901 / 250000000) ≤ -Real.log (36341 / 100000) ∧
    -Real.log (36341 / 100000) ≤ (506111803 / 500000000) := by
  have h := checkLog_sound (w := (13659 / 86341)) (n := 12)
    (lo := (39884553 / 125000000)) (hi := (12763057 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36341) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 36341) = 1/(36341 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15138 : Bounds (-506111803 / 500000000) (-253055901 / 250000000) (Real.log (36341 / 100000)) := by
  have h := reflection_log_15138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15139_neg : (129902199 / 250000000) ≤ -Real.log (5947531719 / 10000000000) ∧
    -Real.log (5947531719 / 10000000000) ≤ (519608797 / 1000000000) := by
  have h := checkLog_sound (w := (4052468281 / 15947531719)) (n := 12)
    (lo := (129902199 / 250000000)) (hi := (519608797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5947531719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5947531719) = 1/(5947531719 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15139 : Bounds (-519608797 / 1000000000) (-129902199 / 250000000) (Real.log (5947531719 / 10000000000)) := by
  have h := reflection_log_15139_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15140_neg : (257654631 / 500000000) ≤ -Real.log (149328959631 / 250000000000) ∧
    -Real.log (149328959631 / 250000000000) ≤ (515309263 / 1000000000) := by
  have h := checkLog_sound (w := (100671040369 / 399328959631)) (n := 12)
    (lo := (257654631 / 500000000)) (hi := (515309263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 149328959631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 149328959631) = 1/(149328959631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15140 : Bounds (-515309263 / 1000000000) (-257654631 / 500000000) (Real.log (149328959631 / 250000000000)) := by
  have h := reflection_log_15140_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15141_neg : (1498073701 / 1000000000) ≤ -Real.log (500000000000 / 2236532156989) ∧
    -Real.log (500000000000 / 2236532156989) ≤ (187259213 / 125000000) := by
  have h := checkLog_sound (w := (236532156989 / 4236532156989)) (n := 12)
    (lo := (111779341 / 1000000000)) (hi := (55889671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2236532156989 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2236532156989 / 2000000000000) = 1/(500000000000 / 2236532156989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15141 : Bounds (1498073701 / 1000000000) (187259213 / 125000000) (Real.log (2236532156989 / 500000000000)) := by
  have h := reflection_log_15141_neg
  have he : Real.log (2236532156989 / 500000000000) = -Real.log (500000000000 / 2236532156989) := by
    rw [show ((2236532156989 / 500000000000) : ℝ) = ((500000000000 / 2236532156989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15142_neg : (1504838413 / 1000000000) ≤ -Real.log (250000000000 / 1125856470653) ∧
    -Real.log (250000000000 / 1125856470653) ≤ (94052401 / 62500000) := by
  have h := checkLog_sound (w := (125856470653 / 2125856470653)) (n := 12)
    (lo := (118544053 / 1000000000)) (hi := (59272027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1125856470653 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1125856470653 / 1000000000000) = 1/(250000000000 / 1125856470653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15142 : Bounds (1504838413 / 1000000000) (94052401 / 62500000) (Real.log (1125856470653 / 250000000000)) := by
  have h := reflection_log_15142_neg
  have he : Real.log (1125856470653 / 250000000000) = -Real.log (250000000000 / 1125856470653) := by
    rw [show ((1125856470653 / 250000000000) : ℝ) = ((250000000000 / 1125856470653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15143_neg : (1221330997 / 250000000) ≤ -Real.log (250000000000 / 33083333333333) ∧
    -Real.log (250000000000 / 33083333333333) ≤ (1221330999 / 250000000) := by
  have h := checkLog_sound (w := (1083333333333 / 65083333333333)) (n := 12)
    (lo := (1040429 / 31250000)) (hi := (33293729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33083333333333 / 32000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(33083333333333 / 32000000000000) = 1/(250000000000 / 33083333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15143 : Bounds (1221330997 / 250000000) (1221330999 / 250000000) (Real.log (33083333333333 / 250000000000)) := by
  have h := reflection_log_15143_neg
  have he : Real.log (33083333333333 / 250000000000) = -Real.log (250000000000 / 33083333333333) := by
    rw [show ((33083333333333 / 250000000000) : ℝ) = ((250000000000 / 33083333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15144_neg : (4954820511 / 1000000000) ≤ -Real.log (125000000000 / 17732142857143) ∧
    -Real.log (125000000000 / 17732142857143) ≤ (4954820519 / 1000000000) := by
  have h := checkLog_sound (w := (1732142857143 / 33732142857143)) (n := 12)
    (lo := (102790251 / 1000000000)) (hi := (25697563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17732142857143 / 16000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(17732142857143 / 16000000000000) = 1/(125000000000 / 17732142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15144 : Bounds (4954820511 / 1000000000) (4954820519 / 1000000000) (Real.log (17732142857143 / 125000000000)) := by
  have h := reflection_log_15144_neg
  have he : Real.log (17732142857143 / 125000000000) = -Real.log (125000000000 / 17732142857143) := by
    rw [show ((17732142857143 / 125000000000) : ℝ) = ((125000000000 / 17732142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15145_neg : (686625963 / 1000000000) ≤ -Real.log (1000 / 1987) ∧
    -Real.log (1000 / 1987) ≤ (171656491 / 250000000) := by
  have h := checkLog_sound (w := (987 / 2987)) (n := 12)
    (lo := (686625963 / 1000000000)) (hi := (171656491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1987 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1987 / 1000) = 1/(1000 / 1987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15145 : Bounds (686625963 / 1000000000) (171656491 / 250000000) (Real.log (1987 / 1000)) := by
  have h := reflection_log_15145_neg
  have he : Real.log (1987 / 1000) = -Real.log (1000 / 1987) := by
    rw [show ((1987 / 1000) : ℝ) = ((1000 / 1987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15146_neg : (2171402959 / 500000000) ≤ -Real.log (13 / 1000) ∧
    -Real.log (13 / 1000) ≤ (173712237 / 40000000) := by
  have h := checkLog_sound (w := (21 / 229)) (n := 12)
    (lo := (91961419 / 500000000)) (hi := (183922839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 104) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(125 / 104) = 1/(13 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15146 : Bounds (-173712237 / 40000000) (-2171402959 / 500000000) (Real.log (13 / 1000)) := by
  have h := reflection_log_15146_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15147_neg : (986513 / 1000000000) ≤ -Real.log (1000000 / 1000987) ∧
    -Real.log (1000000 / 1000987) ≤ (493257 / 500000000) := by
  have h := checkLog_sound (w := (987 / 2000987)) (n := 12)
    (lo := (986513 / 1000000000)) (hi := (493257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000987 / 1000000) = 1/(1000000 / 1000987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15147 : Bounds (986513 / 1000000000) (493257 / 500000000) (Real.log (1000987 / 1000000)) := by
  have h := reflection_log_15147_neg
  have he : Real.log (1000987 / 1000000) = -Real.log (1000000 / 1000987) := by
    rw [show ((1000987 / 1000000) : ℝ) = ((1000000 / 1000987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15148_neg : (987487 / 1000000000) ≤ -Real.log (999013 / 1000000) ∧
    -Real.log (999013 / 1000000) ≤ (30859 / 31250000) := by
  have h := checkLog_sound (w := (987 / 1999013)) (n := 12)
    (lo := (987487 / 1000000000)) (hi := (30859 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999013) = 1/(999013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15148 : Bounds (-30859 / 31250000) (-987487 / 1000000000) (Real.log (999013 / 1000000)) := by
  have h := reflection_log_15148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15149_neg : (492226731 / 1000000000) ≤ -Real.log (200000 / 327191) ∧
    -Real.log (200000 / 327191) ≤ (123056683 / 250000000) := by
  have h := checkLog_sound (w := (127191 / 527191)) (n := 12)
    (lo := (492226731 / 1000000000)) (hi := (123056683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327191 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327191 / 200000) = 1/(200000 / 327191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15149 : Bounds (492226731 / 1000000000) (123056683 / 250000000) (Real.log (327191 / 200000)) := by
  have h := reflection_log_15149_neg
  have he : Real.log (327191 / 200000) = -Real.log (200000 / 327191) := by
    rw [show ((327191 / 200000) : ℝ) = ((200000 / 327191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15150_neg : (31577431 / 31250000) ≤ -Real.log (72809 / 200000) ∧
    -Real.log (72809 / 200000) ≤ (505238897 / 500000000) := by
  have h := checkLog_sound (w := (27191 / 172809)) (n := 12)
    (lo := (79332653 / 250000000)) (hi := (317330613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 72809) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 72809) = 1/(72809 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15150 : Bounds (-505238897 / 500000000) (-31577431 / 31250000) (Real.log (72809 / 200000)) := by
  have h := reflection_log_15150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15151_neg : (30841753 / 62500000) ≤ -Real.log (1000000 / 1637987) ∧
    -Real.log (1000000 / 1637987) ≤ (493468049 / 1000000000) := by
  have h := checkLog_sound (w := (637987 / 2637987)) (n := 12)
    (lo := (30841753 / 62500000)) (hi := (493468049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1637987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1637987 / 1000000) = 1/(1000000 / 1637987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15151 : Bounds (30841753 / 62500000) (493468049 / 1000000000) (Real.log (1637987 / 1000000)) := by
  have h := reflection_log_15151_neg
  have he : Real.log (1637987 / 1000000) = -Real.log (1000000 / 1637987) := by
    rw [show ((1637987 / 1000000) : ℝ) = ((1000000 / 1637987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15152_neg : (203215031 / 200000000) ≤ -Real.log (362013 / 1000000) ∧
    -Real.log (362013 / 1000000) ≤ (1016075157 / 1000000000) := by
  have h := checkLog_sound (w := (137987 / 862013)) (n := 12)
    (lo := (12917119 / 40000000)) (hi := (40365997 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 362013) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 362013) = 1/(362013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15152 : Bounds (-1016075157 / 1000000000) (-203215031 / 200000000) (Real.log (362013 / 1000000)) := by
  have h := reflection_log_15152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15153_neg : (522607107 / 1000000000) ≤ -Real.log (592972587831 / 1000000000000) ∧
    -Real.log (592972587831 / 1000000000000) ≤ (130651777 / 250000000) := by
  have h := checkLog_sound (w := (407027412169 / 1592972587831)) (n := 12)
    (lo := (522607107 / 1000000000)) (hi := (130651777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 592972587831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 592972587831) = 1/(592972587831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15153 : Bounds (-130651777 / 250000000) (-522607107 / 1000000000) (Real.log (592972587831 / 1000000000000)) := by
  have h := reflection_log_15153_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15154_neg : (25912553 / 50000000) ≤ -Real.log (23822449519 / 40000000000) ∧
    -Real.log (23822449519 / 40000000000) ≤ (518251061 / 1000000000) := by
  have h := checkLog_sound (w := (16177550481 / 63822449519)) (n := 12)
    (lo := (25912553 / 50000000)) (hi := (518251061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 23822449519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 23822449519) = 1/(23822449519 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15154 : Bounds (-518251061 / 1000000000) (-25912553 / 50000000) (Real.log (23822449519 / 40000000000)) := by
  have h := reflection_log_15154_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15155_neg : (1502704523 / 1000000000) ≤ -Real.log (25000000000 / 112345657817) ∧
    -Real.log (25000000000 / 112345657817) ≤ (751352263 / 500000000) := by
  have h := checkLog_sound (w := (12345657817 / 212345657817)) (n := 12)
    (lo := (116410163 / 1000000000)) (hi := (29102541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112345657817 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(112345657817 / 100000000000) = 1/(25000000000 / 112345657817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15155 : Bounds (1502704523 / 1000000000) (751352263 / 500000000) (Real.log (112345657817 / 25000000000)) := by
  have h := reflection_log_15155_neg
  have he : Real.log (112345657817 / 25000000000) = -Real.log (25000000000 / 112345657817) := by
    rw [show ((112345657817 / 25000000000) : ℝ) = ((25000000000 / 112345657817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15156_neg : (1509543203 / 1000000000) ≤ -Real.log (125000000000 / 565582934867) ∧
    -Real.log (125000000000 / 565582934867) ≤ (754771603 / 500000000) := by
  have h := checkLog_sound (w := (65582934867 / 1065582934867)) (n := 12)
    (lo := (123248843 / 1000000000)) (hi := (30812211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565582934867 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(565582934867 / 500000000000) = 1/(125000000000 / 565582934867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15156 : Bounds (1509543203 / 1000000000) (754771603 / 500000000) (Real.log (565582934867 / 125000000000)) := by
  have h := reflection_log_15156_neg
  have he : Real.log (565582934867 / 125000000000) = -Real.log (125000000000 / 565582934867) := by
    rw [show ((565582934867 / 125000000000) : ℝ) = ((125000000000 / 565582934867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15157_neg : (4954820511 / 1000000000) ≤ -Real.log (500000000000 / 70928571428571) ∧
    -Real.log (500000000000 / 70928571428571) ≤ (4954820519 / 1000000000) := by
  have h := checkLog_sound (w := (6928571428571 / 134928571428571)) (n := 12)
    (lo := (102790251 / 1000000000)) (hi := (25697563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70928571428571 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(70928571428571 / 64000000000000) = 1/(500000000000 / 70928571428571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15157 : Bounds (4954820511 / 1000000000) (4954820519 / 1000000000) (Real.log (70928571428571 / 500000000000)) := by
  have h := reflection_log_15157_neg
  have he : Real.log (70928571428571 / 500000000000) = -Real.log (500000000000 / 70928571428571) := by
    rw [show ((70928571428571 / 500000000000) : ℝ) = ((500000000000 / 70928571428571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15158_neg : (5029431881 / 1000000000) ≤ -Real.log (500000000000 / 76423076923077) ∧
    -Real.log (500000000000 / 76423076923077) ≤ (5029431889 / 1000000000) := by
  have h := checkLog_sound (w := (12423076923077 / 140423076923077)) (n := 12)
    (lo := (177401621 / 1000000000)) (hi := (88700811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76423076923077 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(76423076923077 / 64000000000000) = 1/(500000000000 / 76423076923077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15158 : Bounds (5029431881 / 1000000000) (5029431889 / 1000000000) (Real.log (76423076923077 / 500000000000)) := by
  have h := reflection_log_15158_neg
  have he : Real.log (76423076923077 / 500000000000) = -Real.log (500000000000 / 76423076923077) := by
    rw [show ((76423076923077 / 500000000000) : ℝ) = ((500000000000 / 76423076923077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15159_neg : (171782277 / 250000000) ≤ -Real.log (250 / 497) ∧
    -Real.log (250 / 497) ≤ (687129109 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 747)) (n := 12)
    (lo := (171782277 / 250000000)) (hi := (687129109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497 / 250) = 1/(250 / 497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15159 : Bounds (171782277 / 250000000) (687129109 / 1000000000) (Real.log (497 / 250)) := by
  have h := reflection_log_15159_neg
  have he : Real.log (497 / 250) = -Real.log (250 / 497) := by
    rw [show ((497 / 250) : ℝ) = ((250 / 497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15160_neg : (35382789 / 8000000) ≤ -Real.log (3 / 250) ∧
    -Real.log (3 / 250) ≤ (552856079 / 125000000) := by
  have h := checkLog_sound (w := (29 / 221)) (n := 12)
    (lo := (52793109 / 200000000)) (hi := (131982773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 96) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(125 / 96) = 1/(3 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15160 : Bounds (-552856079 / 125000000) (-35382789 / 8000000) (Real.log (3 / 250)) := by
  have h := reflection_log_15160_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15161_neg : (123439 / 125000000) ≤ -Real.log (250000 / 250247) ∧
    -Real.log (250000 / 250247) ≤ (987513 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 500247)) (n := 12)
    (lo := (123439 / 125000000)) (hi := (987513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250247 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250247 / 250000) = 1/(250000 / 250247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15161 : Bounds (123439 / 125000000) (987513 / 1000000000) (Real.log (250247 / 250000)) := by
  have h := reflection_log_15161_neg
  have he : Real.log (250247 / 250000) = -Real.log (250000 / 250247) := by
    rw [show ((250247 / 250000) : ℝ) = ((250000 / 250247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15162_neg : (123561 / 125000000) ≤ -Real.log (249753 / 250000) ∧
    -Real.log (249753 / 250000) ≤ (988489 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 499753)) (n := 12)
    (lo := (123561 / 125000000)) (hi := (988489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249753) = 1/(249753 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15162 : Bounds (-988489 / 1000000000) (-123561 / 125000000) (Real.log (249753 / 250000)) := by
  have h := reflection_log_15162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15163_neg : (493080913 / 1000000000) ≤ -Real.log (1000000 / 1637353) ∧
    -Real.log (1000000 / 1637353) ≤ (246540457 / 500000000) := by
  have h := checkLog_sound (w := (637353 / 2637353)) (n := 12)
    (lo := (493080913 / 1000000000)) (hi := (246540457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1637353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1637353 / 1000000) = 1/(1000000 / 1637353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15163 : Bounds (493080913 / 1000000000) (246540457 / 500000000) (Real.log (1637353 / 1000000)) := by
  have h := reflection_log_15163_neg
  have he : Real.log (1637353 / 1000000) = -Real.log (1000000 / 1637353) := by
    rw [show ((1637353 / 1000000) : ℝ) = ((1000000 / 1637353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15164_neg : (1014325369 / 1000000000) ≤ -Real.log (362647 / 1000000) ∧
    -Real.log (362647 / 1000000) ≤ (1014325371 / 1000000000) := by
  have h := checkLog_sound (w := (137353 / 862647)) (n := 12)
    (lo := (321178189 / 1000000000)) (hi := (32117819 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 362647) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 362647) = 1/(362647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15164 : Bounds (-1014325371 / 1000000000) (-1014325369 / 1000000000) (Real.log (362647 / 1000000)) := by
  have h := reflection_log_15164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15165_neg : (494331541 / 1000000000) ≤ -Real.log (500000 / 819701) ∧
    -Real.log (500000 / 819701) ≤ (247165771 / 500000000) := by
  have h := checkLog_sound (w := (319701 / 1319701)) (n := 12)
    (lo := (494331541 / 1000000000)) (hi := (247165771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819701 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819701 / 500000) = 1/(500000 / 819701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15165 : Bounds (494331541 / 1000000000) (247165771 / 500000000) (Real.log (819701 / 500000)) := by
  have h := reflection_log_15165_neg
  have he : Real.log (819701 / 500000) = -Real.log (500000 / 819701) := by
    rw [show ((819701 / 500000) : ℝ) = ((500000 / 819701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15166_neg : (1019991513 / 1000000000) ≤ -Real.log (180299 / 500000) ∧
    -Real.log (180299 / 500000) ≤ (203998303 / 200000000) := by
  have h := checkLog_sound (w := (69701 / 430299)) (n := 12)
    (lo := (326844333 / 1000000000)) (hi := (163422167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 180299) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 180299) = 1/(180299 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15166 : Bounds (-203998303 / 200000000) (-1019991513 / 1000000000) (Real.log (180299 / 500000)) := by
  have h := reflection_log_15166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15167_neg : (525659973 / 1000000000) ≤ -Real.log (147791270599 / 250000000000) ∧
    -Real.log (147791270599 / 250000000000) ≤ (262829987 / 500000000) := by
  have h := checkLog_sound (w := (102208729401 / 397791270599)) (n := 12)
    (lo := (525659973 / 1000000000)) (hi := (262829987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 147791270599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 147791270599) = 1/(147791270599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15167 : Bounds (-262829987 / 500000000) (-525659973 / 1000000000) (Real.log (147791270599 / 250000000000)) := by
  have h := reflection_log_15167_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
