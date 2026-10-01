import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7232_neg : (26522559 / 125000000) ≤ -Real.log (500000000000 / 618185498029) ∧
    -Real.log (500000000000 / 618185498029) ≤ (212180473 / 1000000000) := by
  have h := checkLog_sound (w := (118185498029 / 1118185498029)) (n := 12)
    (lo := (26522559 / 125000000)) (hi := (212180473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618185498029 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618185498029 / 500000000000) = 1/(500000000000 / 618185498029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7232 : Bounds (26522559 / 125000000) (212180473 / 1000000000) (Real.log (618185498029 / 500000000000)) := by
  have h := reflection_log_7232_neg
  have he : Real.log (618185498029 / 500000000000) = -Real.log (500000000000 / 618185498029) := by
    rw [show ((618185498029 / 500000000000) : ℝ) = ((500000000000 / 618185498029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7233_neg : (212125441 / 500000000) ≤ -Real.log (12500000000 / 19105562579) ∧
    -Real.log (12500000000 / 19105562579) ≤ (424250883 / 1000000000) := by
  have h := checkLog_sound (w := (6605562579 / 31605562579)) (n := 12)
    (lo := (212125441 / 500000000)) (hi := (424250883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19105562579 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19105562579 / 12500000000) = 1/(12500000000 / 19105562579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7233 : Bounds (212125441 / 500000000) (424250883 / 1000000000) (Real.log (19105562579 / 12500000000)) := by
  have h := reflection_log_7233_neg
  have he : Real.log (19105562579 / 12500000000) = -Real.log (12500000000 / 19105562579) := by
    rw [show ((19105562579 / 12500000000) : ℝ) = ((12500000000 / 19105562579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7234_neg : (425296673 / 1000000000) ≤ -Real.log (15625000000 / 23906941809) ∧
    -Real.log (15625000000 / 23906941809) ≤ (212648337 / 500000000) := by
  have h := checkLog_sound (w := (8281941809 / 39531941809)) (n := 12)
    (lo := (425296673 / 1000000000)) (hi := (212648337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23906941809 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23906941809 / 15625000000) = 1/(15625000000 / 23906941809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7234 : Bounds (425296673 / 1000000000) (212648337 / 500000000) (Real.log (23906941809 / 15625000000)) := by
  have h := reflection_log_7234_neg
  have he : Real.log (23906941809 / 15625000000) = -Real.log (15625000000 / 23906941809) := by
    rw [show ((23906941809 / 15625000000) : ℝ) = ((15625000000 / 23906941809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7235_neg : (190620359 / 1000000000) ≤ -Real.log (100 / 121) ∧
    -Real.log (100 / 121) ≤ (4765509 / 25000000) := by
  have h := checkLog_sound (w := (21 / 221)) (n := 12)
    (lo := (190620359 / 1000000000)) (hi := (4765509 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121 / 100) = 1/(100 / 121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7235 : Bounds (190620359 / 1000000000) (4765509 / 25000000) (Real.log (121 / 100)) := by
  have h := reflection_log_7235_neg
  have he : Real.log (121 / 100) = -Real.log (100 / 121) := by
    rw [show ((121 / 100) : ℝ) = ((100 / 121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7236_neg : (235722333 / 1000000000) ≤ -Real.log (79 / 100) ∧
    -Real.log (79 / 100) ≤ (117861167 / 500000000) := by
  have h := checkLog_sound (w := (21 / 179)) (n := 12)
    (lo := (235722333 / 1000000000)) (hi := (117861167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 79) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 79) = 1/(79 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7236 : Bounds (-117861167 / 500000000) (-235722333 / 1000000000) (Real.log (79 / 100)) := by
  have h := reflection_log_7236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7237_neg : (209977 / 1000000000) ≤ -Real.log (100000 / 100021) ∧
    -Real.log (100000 / 100021) ≤ (104989 / 500000000) := by
  have h := checkLog_sound (w := (21 / 200021)) (n := 12)
    (lo := (209977 / 1000000000)) (hi := (104989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100021 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100021 / 100000) = 1/(100000 / 100021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7237 : Bounds (209977 / 1000000000) (104989 / 500000000) (Real.log (100021 / 100000)) := by
  have h := reflection_log_7237_neg
  have he : Real.log (100021 / 100000) = -Real.log (100000 / 100021) := by
    rw [show ((100021 / 100000) : ℝ) = ((100000 / 100021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7238_neg : (105011 / 500000000) ≤ -Real.log (99979 / 100000) ∧
    -Real.log (99979 / 100000) ≤ (210023 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 199979)) (n := 12)
    (lo := (105011 / 500000000)) (hi := (210023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99979) = 1/(99979 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7238 : Bounds (-210023 / 1000000000) (-105011 / 500000000) (Real.log (99979 / 100000)) := by
  have h := reflection_log_7238_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7239_neg : (100285057 / 1000000000) ≤ -Real.log (500000 / 552743) ∧
    -Real.log (500000 / 552743) ≤ (50142529 / 500000000) := by
  have h := checkLog_sound (w := (52743 / 1052743)) (n := 12)
    (lo := (100285057 / 1000000000)) (hi := (50142529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552743 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(552743 / 500000) = 1/(500000 / 552743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7239 : Bounds (100285057 / 1000000000) (50142529 / 500000000) (Real.log (552743 / 500000)) := by
  have h := reflection_log_7239_neg
  have he : Real.log (552743 / 500000) = -Real.log (500000 / 552743) := by
    rw [show ((552743 / 500000) : ℝ) = ((500000 / 552743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7240_neg : (27868681 / 250000000) ≤ -Real.log (447257 / 500000) ∧
    -Real.log (447257 / 500000) ≤ (4458989 / 40000000) := by
  have h := checkLog_sound (w := (52743 / 947257)) (n := 12)
    (lo := (27868681 / 250000000)) (hi := (4458989 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 447257) = 1/(447257 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7240 : Bounds (-4458989 / 40000000) (-27868681 / 250000000) (Real.log (447257 / 500000)) := by
  have h := reflection_log_7240_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7241_neg : (50352799 / 500000000) ≤ -Real.log (1000000 / 1105951) ∧
    -Real.log (1000000 / 1105951) ≤ (100705599 / 1000000000) := by
  have h := checkLog_sound (w := (105951 / 2105951)) (n := 12)
    (lo := (50352799 / 500000000)) (hi := (100705599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1105951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1105951 / 1000000) = 1/(1000000 / 1105951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7241 : Bounds (50352799 / 500000000) (100705599 / 1000000000) (Real.log (1105951 / 1000000)) := by
  have h := reflection_log_7241_neg
  have he : Real.log (1105951 / 1000000) = -Real.log (1000000 / 1105951) := by
    rw [show ((1105951 / 1000000) : ℝ) = ((1000000 / 1105951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7242_neg : (22398939 / 200000000) ≤ -Real.log (894049 / 1000000) ∧
    -Real.log (894049 / 1000000) ≤ (13999337 / 125000000) := by
  have h := checkLog_sound (w := (105951 / 1894049)) (n := 12)
    (lo := (22398939 / 200000000)) (hi := (13999337 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 894049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 894049) = 1/(894049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7242 : Bounds (-13999337 / 125000000) (-22398939 / 200000000) (Real.log (894049 / 1000000)) := by
  have h := reflection_log_7242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7243_neg : (11289097 / 1000000000) ≤ -Real.log (988774385599 / 1000000000000) ∧
    -Real.log (988774385599 / 1000000000000) ≤ (5644549 / 500000000) := by
  have h := checkLog_sound (w := (11225614401 / 1988774385599)) (n := 12)
    (lo := (11289097 / 1000000000)) (hi := (5644549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988774385599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988774385599) = 1/(988774385599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7243 : Bounds (-5644549 / 500000000) (-11289097 / 1000000000) (Real.log (988774385599 / 1000000000000)) := by
  have h := reflection_log_7243_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7244_neg : (11189667 / 1000000000) ≤ -Real.log (247218175951 / 250000000000) ∧
    -Real.log (247218175951 / 250000000000) ≤ (2797417 / 250000000) := by
  have h := checkLog_sound (w := (2781824049 / 497218175951)) (n := 12)
    (lo := (11189667 / 1000000000)) (hi := (2797417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247218175951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247218175951) = 1/(247218175951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7244 : Bounds (-2797417 / 250000000) (-11189667 / 1000000000) (Real.log (247218175951 / 250000000000)) := by
  have h := reflection_log_7244_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7245_neg : (105879891 / 500000000) ≤ -Real.log (50000000000 / 61792548803) ∧
    -Real.log (50000000000 / 61792548803) ≤ (211759783 / 1000000000) := by
  have h := checkLog_sound (w := (11792548803 / 111792548803)) (n := 12)
    (lo := (105879891 / 500000000)) (hi := (211759783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61792548803 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61792548803 / 50000000000) = 1/(50000000000 / 61792548803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7245 : Bounds (105879891 / 500000000) (211759783 / 1000000000) (Real.log (61792548803 / 50000000000)) := by
  have h := reflection_log_7245_neg
  have he : Real.log (61792548803 / 50000000000) = -Real.log (50000000000 / 61792548803) := by
    rw [show ((61792548803 / 50000000000) : ℝ) = ((50000000000 / 61792548803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7246_neg : (212700293 / 1000000000) ≤ -Real.log (500000000000 / 618506927473) ∧
    -Real.log (500000000000 / 618506927473) ≤ (106350147 / 500000000) := by
  have h := checkLog_sound (w := (118506927473 / 1118506927473)) (n := 12)
    (lo := (212700293 / 1000000000)) (hi := (106350147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618506927473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618506927473 / 500000000000) = 1/(500000000000 / 618506927473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7246 : Bounds (212700293 / 1000000000) (106350147 / 500000000) (Real.log (618506927473 / 500000000000)) := by
  have h := reflection_log_7246_neg
  have he : Real.log (618506927473 / 500000000000) = -Real.log (500000000000 / 618506927473) := by
    rw [show ((618506927473 / 500000000000) : ℝ) = ((500000000000 / 618506927473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7247_neg : (425296673 / 1000000000) ≤ -Real.log (500000000000 / 765022137887) ∧
    -Real.log (500000000000 / 765022137887) ≤ (212648337 / 500000000) := by
  have h := checkLog_sound (w := (265022137887 / 1265022137887)) (n := 12)
    (lo := (425296673 / 1000000000)) (hi := (212648337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765022137887 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(765022137887 / 500000000000) = 1/(500000000000 / 765022137887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7247 : Bounds (425296673 / 1000000000) (212648337 / 500000000) (Real.log (765022137887 / 500000000000)) := by
  have h := reflection_log_7247_neg
  have he : Real.log (765022137887 / 500000000000) = -Real.log (500000000000 / 765022137887) := by
    rw [show ((765022137887 / 500000000000) : ℝ) = ((500000000000 / 765022137887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7248_neg : (426342693 / 1000000000) ≤ -Real.log (500000000000 / 765822784811) ∧
    -Real.log (500000000000 / 765822784811) ≤ (213171347 / 500000000) := by
  have h := checkLog_sound (w := (265822784811 / 1265822784811)) (n := 12)
    (lo := (426342693 / 1000000000)) (hi := (213171347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765822784811 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(765822784811 / 500000000000) = 1/(500000000000 / 765822784811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7248 : Bounds (426342693 / 1000000000) (213171347 / 500000000) (Real.log (765822784811 / 500000000000)) := by
  have h := reflection_log_7248_neg
  have he : Real.log (765822784811 / 500000000000) = -Real.log (500000000000 / 765822784811) := by
    rw [show ((765822784811 / 500000000000) : ℝ) = ((500000000000 / 765822784811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7249_neg : (191033497 / 1000000000) ≤ -Real.log (2000 / 2421) ∧
    -Real.log (2000 / 2421) ≤ (95516749 / 500000000) := by
  have h := checkLog_sound (w := (421 / 4421)) (n := 12)
    (lo := (191033497 / 1000000000)) (hi := (95516749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2421 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2421 / 2000) = 1/(2000 / 2421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7249 : Bounds (191033497 / 1000000000) (95516749 / 500000000) (Real.log (2421 / 2000)) := by
  have h := reflection_log_7249_neg
  have he : Real.log (2421 / 2000) = -Real.log (2000 / 2421) := by
    rw [show ((2421 / 2000) : ℝ) = ((2000 / 2421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7250_neg : (47271089 / 200000000) ≤ -Real.log (1579 / 2000) ∧
    -Real.log (1579 / 2000) ≤ (118177723 / 500000000) := by
  have h := checkLog_sound (w := (421 / 3579)) (n := 12)
    (lo := (47271089 / 200000000)) (hi := (118177723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1579) = 1/(1579 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7250 : Bounds (-118177723 / 500000000) (-47271089 / 200000000) (Real.log (1579 / 2000)) := by
  have h := reflection_log_7250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7251_neg : (210477 / 1000000000) ≤ -Real.log (2000000 / 2000421) ∧
    -Real.log (2000000 / 2000421) ≤ (105239 / 500000000) := by
  have h := checkLog_sound (w := (421 / 4000421)) (n := 12)
    (lo := (210477 / 1000000000)) (hi := (105239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000421 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000421 / 2000000) = 1/(2000000 / 2000421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7251 : Bounds (210477 / 1000000000) (105239 / 500000000) (Real.log (2000421 / 2000000)) := by
  have h := reflection_log_7251_neg
  have he : Real.log (2000421 / 2000000) = -Real.log (2000000 / 2000421) := by
    rw [show ((2000421 / 2000000) : ℝ) = ((2000000 / 2000421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7252_neg : (105261 / 500000000) ≤ -Real.log (1999579 / 2000000) ∧
    -Real.log (1999579 / 2000000) ≤ (210523 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 3999579)) (n := 12)
    (lo := (105261 / 500000000)) (hi := (210523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999579) = 1/(1999579 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7252 : Bounds (-210523 / 1000000000) (-105261 / 500000000) (Real.log (1999579 / 2000000)) := by
  have h := reflection_log_7252_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7253_neg : (50257849 / 500000000) ≤ -Real.log (1000000 / 1105741) ∧
    -Real.log (1000000 / 1105741) ≤ (100515699 / 1000000000) := by
  have h := checkLog_sound (w := (105741 / 2105741)) (n := 12)
    (lo := (50257849 / 500000000)) (hi := (100515699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1105741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1105741 / 1000000) = 1/(1000000 / 1105741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7253 : Bounds (50257849 / 500000000) (100515699 / 1000000000) (Real.log (1105741 / 1000000)) := by
  have h := reflection_log_7253_neg
  have he : Real.log (1105741 / 1000000) = -Real.log (1000000 / 1105741) := by
    rw [show ((1105741 / 1000000) : ℝ) = ((1000000 / 1105741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7254_neg : (27939959 / 250000000) ≤ -Real.log (894259 / 1000000) ∧
    -Real.log (894259 / 1000000) ≤ (111759837 / 1000000000) := by
  have h := checkLog_sound (w := (105741 / 1894259)) (n := 12)
    (lo := (27939959 / 250000000)) (hi := (111759837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 894259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 894259) = 1/(894259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7254 : Bounds (-111759837 / 1000000000) (-27939959 / 250000000) (Real.log (894259 / 1000000)) := by
  have h := reflection_log_7254_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7255_neg : (50468523 / 500000000) ≤ -Real.log (1000000 / 1106207) ∧
    -Real.log (1000000 / 1106207) ≤ (100937047 / 1000000000) := by
  have h := checkLog_sound (w := (106207 / 2106207)) (n := 12)
    (lo := (50468523 / 500000000)) (hi := (100937047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1106207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1106207 / 1000000) = 1/(1000000 / 1106207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7255 : Bounds (50468523 / 500000000) (100937047 / 1000000000) (Real.log (1106207 / 1000000)) := by
  have h := reflection_log_7255_neg
  have he : Real.log (1106207 / 1000000) = -Real.log (1000000 / 1106207) := by
    rw [show ((1106207 / 1000000) : ℝ) = ((1000000 / 1106207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7256_neg : (56140537 / 500000000) ≤ -Real.log (893793 / 1000000) ∧
    -Real.log (893793 / 1000000) ≤ (4491243 / 40000000) := by
  have h := checkLog_sound (w := (106207 / 1893793)) (n := 12)
    (lo := (56140537 / 500000000)) (hi := (4491243 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 893793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 893793) = 1/(893793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7256 : Bounds (-4491243 / 40000000) (-56140537 / 500000000) (Real.log (893793 / 1000000)) := by
  have h := reflection_log_7256_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7257_neg : (11344027 / 1000000000) ≤ -Real.log (988720073151 / 1000000000000) ∧
    -Real.log (988720073151 / 1000000000000) ≤ (2836007 / 250000000) := by
  have h := checkLog_sound (w := (11279926849 / 1988720073151)) (n := 12)
    (lo := (11344027 / 1000000000)) (hi := (2836007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988720073151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988720073151) = 1/(988720073151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7257 : Bounds (-2836007 / 250000000) (-11344027 / 1000000000) (Real.log (988720073151 / 1000000000000)) := by
  have h := reflection_log_7257_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7258_neg : (5622069 / 500000000) ≤ -Real.log (988818840919 / 1000000000000) ∧
    -Real.log (988818840919 / 1000000000000) ≤ (11244139 / 1000000000) := by
  have h := checkLog_sound (w := (11181159081 / 1988818840919)) (n := 12)
    (lo := (5622069 / 500000000)) (hi := (11244139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988818840919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988818840919) = 1/(988818840919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7258 : Bounds (-11244139 / 1000000000) (-5622069 / 500000000) (Real.log (988818840919 / 1000000000000)) := by
  have h := reflection_log_7258_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7259_neg : (42455107 / 200000000) ≤ -Real.log (500000000000 / 618244267041) ∧
    -Real.log (500000000000 / 618244267041) ≤ (13267221 / 62500000) := by
  have h := checkLog_sound (w := (118244267041 / 1118244267041)) (n := 12)
    (lo := (42455107 / 200000000)) (hi := (13267221 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618244267041 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618244267041 / 500000000000) = 1/(500000000000 / 618244267041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7259 : Bounds (42455107 / 200000000) (13267221 / 62500000) (Real.log (618244267041 / 500000000000)) := by
  have h := reflection_log_7259_neg
  have he : Real.log (618244267041 / 500000000000) = -Real.log (500000000000 / 618244267041) := by
    rw [show ((618244267041 / 500000000000) : ℝ) = ((500000000000 / 618244267041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7260_neg : (5330453 / 25000000) ≤ -Real.log (125000000000 / 154706822497) ∧
    -Real.log (125000000000 / 154706822497) ≤ (213218121 / 1000000000) := by
  have h := checkLog_sound (w := (29706822497 / 279706822497)) (n := 12)
    (lo := (5330453 / 25000000)) (hi := (213218121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154706822497 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154706822497 / 125000000000) = 1/(125000000000 / 154706822497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7260 : Bounds (5330453 / 25000000) (213218121 / 1000000000) (Real.log (154706822497 / 125000000000)) := by
  have h := reflection_log_7260_neg
  have he : Real.log (154706822497 / 125000000000) = -Real.log (125000000000 / 154706822497) := by
    rw [show ((154706822497 / 125000000000) : ℝ) = ((125000000000 / 154706822497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7261_neg : (426342693 / 1000000000) ≤ -Real.log (50000000000 / 76582278481) ∧
    -Real.log (50000000000 / 76582278481) ≤ (213171347 / 500000000) := by
  have h := checkLog_sound (w := (26582278481 / 126582278481)) (n := 12)
    (lo := (426342693 / 1000000000)) (hi := (213171347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76582278481 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76582278481 / 50000000000) = 1/(50000000000 / 76582278481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7261 : Bounds (426342693 / 1000000000) (213171347 / 500000000) (Real.log (76582278481 / 50000000000)) := by
  have h := reflection_log_7261_neg
  have he : Real.log (76582278481 / 50000000000) = -Real.log (50000000000 / 76582278481) := by
    rw [show ((76582278481 / 50000000000) : ℝ) = ((50000000000 / 76582278481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7262_neg : (213694471 / 500000000) ≤ -Real.log (125000000000 / 191656111463) ∧
    -Real.log (125000000000 / 191656111463) ≤ (427388943 / 1000000000) := by
  have h := checkLog_sound (w := (66656111463 / 316656111463)) (n := 12)
    (lo := (213694471 / 500000000)) (hi := (427388943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191656111463 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191656111463 / 125000000000) = 1/(125000000000 / 191656111463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7262 : Bounds (213694471 / 500000000) (427388943 / 1000000000) (Real.log (191656111463 / 125000000000)) := by
  have h := reflection_log_7262_neg
  have he : Real.log (191656111463 / 125000000000) = -Real.log (125000000000 / 191656111463) := by
    rw [show ((191656111463 / 125000000000) : ℝ) = ((125000000000 / 191656111463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7263_neg : (2991351 / 15625000) ≤ -Real.log (1000 / 1211) ∧
    -Real.log (1000 / 1211) ≤ (38289293 / 200000000) := by
  have h := checkLog_sound (w := (211 / 2211)) (n := 12)
    (lo := (2991351 / 15625000)) (hi := (38289293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211 / 1000) = 1/(1000 / 1211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7263 : Bounds (2991351 / 15625000) (38289293 / 200000000) (Real.log (1211 / 1000)) := by
  have h := reflection_log_7263_neg
  have he : Real.log (1211 / 1000) = -Real.log (1000 / 1211) := by
    rw [show ((1211 / 1000) : ℝ) = ((1000 / 1211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7264_neg : (118494479 / 500000000) ≤ -Real.log (789 / 1000) ∧
    -Real.log (789 / 1000) ≤ (236988959 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1789)) (n := 12)
    (lo := (118494479 / 500000000)) (hi := (236988959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 789) = 1/(789 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7264 : Bounds (-236988959 / 1000000000) (-118494479 / 500000000) (Real.log (789 / 1000)) := by
  have h := reflection_log_7264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7265_neg : (210977 / 1000000000) ≤ -Real.log (1000000 / 1000211) ∧
    -Real.log (1000000 / 1000211) ≤ (105489 / 500000000) := by
  have h := checkLog_sound (w := (211 / 2000211)) (n := 12)
    (lo := (210977 / 1000000000)) (hi := (105489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000211 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000211 / 1000000) = 1/(1000000 / 1000211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7265 : Bounds (210977 / 1000000000) (105489 / 500000000) (Real.log (1000211 / 1000000)) := by
  have h := reflection_log_7265_neg
  have he : Real.log (1000211 / 1000000) = -Real.log (1000000 / 1000211) := by
    rw [show ((1000211 / 1000000) : ℝ) = ((1000000 / 1000211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7266_neg : (105511 / 500000000) ≤ -Real.log (999789 / 1000000) ∧
    -Real.log (999789 / 1000000) ≤ (211023 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1999789)) (n := 12)
    (lo := (105511 / 500000000)) (hi := (211023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999789) = 1/(999789 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7266 : Bounds (-211023 / 1000000000) (-105511 / 500000000) (Real.log (999789 / 1000000)) := by
  have h := reflection_log_7266_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7267_neg : (10074719 / 100000000) ≤ -Real.log (1000000 / 1105997) ∧
    -Real.log (1000000 / 1105997) ≤ (100747191 / 1000000000) := by
  have h := checkLog_sound (w := (105997 / 2105997)) (n := 12)
    (lo := (10074719 / 100000000)) (hi := (100747191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1105997 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1105997 / 1000000) = 1/(1000000 / 1105997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7267 : Bounds (10074719 / 100000000) (100747191 / 1000000000) (Real.log (1105997 / 1000000)) := by
  have h := reflection_log_7267_neg
  have he : Real.log (1105997 / 1000000) = -Real.log (1000000 / 1105997) := by
    rw [show ((1105997 / 1000000) : ℝ) = ((1000000 / 1105997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7268_neg : (28011537 / 250000000) ≤ -Real.log (894003 / 1000000) ∧
    -Real.log (894003 / 1000000) ≤ (112046149 / 1000000000) := by
  have h := checkLog_sound (w := (105997 / 1894003)) (n := 12)
    (lo := (28011537 / 250000000)) (hi := (112046149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 894003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 894003) = 1/(894003 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7268 : Bounds (-112046149 / 1000000000) (-28011537 / 250000000) (Real.log (894003 / 1000000)) := by
  have h := reflection_log_7268_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7269_neg : (101168441 / 1000000000) ≤ -Real.log (1000000 / 1106463) ∧
    -Real.log (1000000 / 1106463) ≤ (50584221 / 500000000) := by
  have h := checkLog_sound (w := (106463 / 2106463)) (n := 12)
    (lo := (101168441 / 1000000000)) (hi := (50584221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1106463 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1106463 / 1000000) = 1/(1000000 / 1106463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7269 : Bounds (101168441 / 1000000000) (50584221 / 500000000) (Real.log (1106463 / 1000000)) := by
  have h := reflection_log_7269_neg
  have he : Real.log (1106463 / 1000000) = -Real.log (1000000 / 1106463) := by
    rw [show ((1106463 / 1000000) : ℝ) = ((1000000 / 1106463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7270_neg : (22513507 / 200000000) ≤ -Real.log (893537 / 1000000) ∧
    -Real.log (893537 / 1000000) ≤ (7035471 / 62500000) := by
  have h := checkLog_sound (w := (106463 / 1893537)) (n := 12)
    (lo := (22513507 / 200000000)) (hi := (7035471 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 893537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 893537) = 1/(893537 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7270 : Bounds (-7035471 / 62500000) (-22513507 / 200000000) (Real.log (893537 / 1000000)) := by
  have h := reflection_log_7270_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7271_neg : (11399093 / 1000000000) ≤ -Real.log (988665629631 / 1000000000000) ∧
    -Real.log (988665629631 / 1000000000000) ≤ (5699547 / 500000000) := by
  have h := checkLog_sound (w := (11334370369 / 1988665629631)) (n := 12)
    (lo := (11399093 / 1000000000)) (hi := (5699547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988665629631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988665629631) = 1/(988665629631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7271 : Bounds (-5699547 / 500000000) (-11399093 / 1000000000) (Real.log (988665629631 / 1000000000000)) := by
  have h := reflection_log_7271_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7272_neg : (11298957 / 1000000000) ≤ -Real.log (988764635991 / 1000000000000) ∧
    -Real.log (988764635991 / 1000000000000) ≤ (5649479 / 500000000) := by
  have h := checkLog_sound (w := (11235364009 / 1988764635991)) (n := 12)
    (lo := (11298957 / 1000000000)) (hi := (5649479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988764635991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988764635991) = 1/(988764635991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7272 : Bounds (-5649479 / 500000000) (-11298957 / 1000000000) (Real.log (988764635991 / 1000000000000)) := by
  have h := reflection_log_7272_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7273_neg : (106396669 / 500000000) ≤ -Real.log (50000000000 / 61856447909) ∧
    -Real.log (50000000000 / 61856447909) ≤ (212793339 / 1000000000) := by
  have h := checkLog_sound (w := (11856447909 / 111856447909)) (n := 12)
    (lo := (106396669 / 500000000)) (hi := (212793339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61856447909 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61856447909 / 50000000000) = 1/(50000000000 / 61856447909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7273 : Bounds (106396669 / 500000000) (212793339 / 1000000000) (Real.log (61856447909 / 50000000000)) := by
  have h := reflection_log_7273_neg
  have he : Real.log (61856447909 / 50000000000) = -Real.log (50000000000 / 61856447909) := by
    rw [show ((61856447909 / 50000000000) : ℝ) = ((50000000000 / 61856447909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7274_neg : (26716997 / 125000000) ≤ -Real.log (62500000000 / 77393479509) ∧
    -Real.log (62500000000 / 77393479509) ≤ (213735977 / 1000000000) := by
  have h := checkLog_sound (w := (14893479509 / 139893479509)) (n := 12)
    (lo := (26716997 / 125000000)) (hi := (213735977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77393479509 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77393479509 / 62500000000) = 1/(62500000000 / 77393479509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7274 : Bounds (26716997 / 125000000) (213735977 / 1000000000) (Real.log (77393479509 / 62500000000)) := by
  have h := reflection_log_7274_neg
  have he : Real.log (77393479509 / 62500000000) = -Real.log (62500000000 / 77393479509) := by
    rw [show ((77393479509 / 62500000000) : ℝ) = ((62500000000 / 77393479509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7275_neg : (213694471 / 500000000) ≤ -Real.log (500000000000 / 766624445851) ∧
    -Real.log (500000000000 / 766624445851) ≤ (427388943 / 1000000000) := by
  have h := checkLog_sound (w := (266624445851 / 1266624445851)) (n := 12)
    (lo := (213694471 / 500000000)) (hi := (427388943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((766624445851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(766624445851 / 500000000000) = 1/(500000000000 / 766624445851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7275 : Bounds (213694471 / 500000000) (427388943 / 1000000000) (Real.log (766624445851 / 500000000000)) := by
  have h := reflection_log_7275_neg
  have he : Real.log (766624445851 / 500000000000) = -Real.log (500000000000 / 766624445851) := by
    rw [show ((766624445851 / 500000000000) : ℝ) = ((500000000000 / 766624445851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7276_neg : (214217711 / 500000000) ≤ -Real.log (500000000000 / 767427122941) ∧
    -Real.log (500000000000 / 767427122941) ≤ (428435423 / 1000000000) := by
  have h := checkLog_sound (w := (267427122941 / 1267427122941)) (n := 12)
    (lo := (214217711 / 500000000)) (hi := (428435423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((767427122941 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(767427122941 / 500000000000) = 1/(500000000000 / 767427122941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7276 : Bounds (214217711 / 500000000) (428435423 / 1000000000) (Real.log (767427122941 / 500000000000)) := by
  have h := reflection_log_7276_neg
  have he : Real.log (767427122941 / 500000000000) = -Real.log (500000000000 / 767427122941) := by
    rw [show ((767427122941 / 500000000000) : ℝ) = ((500000000000 / 767427122941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7277_neg : (191859261 / 1000000000) ≤ -Real.log (2000 / 2423) ∧
    -Real.log (2000 / 2423) ≤ (95929631 / 500000000) := by
  have h := checkLog_sound (w := (423 / 4423)) (n := 12)
    (lo := (191859261 / 1000000000)) (hi := (95929631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2423 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2423 / 2000) = 1/(2000 / 2423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7277 : Bounds (191859261 / 1000000000) (95929631 / 500000000) (Real.log (2423 / 2000)) := by
  have h := reflection_log_7277_neg
  have he : Real.log (2423 / 2000) = -Real.log (2000 / 2423) := by
    rw [show ((2423 / 2000) : ℝ) = ((2000 / 2423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7278_neg : (29702859 / 125000000) ≤ -Real.log (1577 / 2000) ∧
    -Real.log (1577 / 2000) ≤ (237622873 / 1000000000) := by
  have h := checkLog_sound (w := (423 / 3577)) (n := 12)
    (lo := (29702859 / 125000000)) (hi := (237622873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1577) = 1/(1577 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7278 : Bounds (-237622873 / 1000000000) (-29702859 / 125000000) (Real.log (1577 / 2000)) := by
  have h := reflection_log_7278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7279_neg : (211477 / 1000000000) ≤ -Real.log (2000000 / 2000423) ∧
    -Real.log (2000000 / 2000423) ≤ (105739 / 500000000) := by
  have h := checkLog_sound (w := (423 / 4000423)) (n := 12)
    (lo := (211477 / 1000000000)) (hi := (105739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000423 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000423 / 2000000) = 1/(2000000 / 2000423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7279 : Bounds (211477 / 1000000000) (105739 / 500000000) (Real.log (2000423 / 2000000)) := by
  have h := reflection_log_7279_neg
  have he : Real.log (2000423 / 2000000) = -Real.log (2000000 / 2000423) := by
    rw [show ((2000423 / 2000000) : ℝ) = ((2000000 / 2000423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7280_neg : (105761 / 500000000) ≤ -Real.log (1999577 / 2000000) ∧
    -Real.log (1999577 / 2000000) ≤ (211523 / 1000000000) := by
  have h := checkLog_sound (w := (423 / 3999577)) (n := 12)
    (lo := (105761 / 500000000)) (hi := (211523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999577) = 1/(1999577 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7280 : Bounds (-211523 / 1000000000) (-105761 / 500000000) (Real.log (1999577 / 2000000)) := by
  have h := reflection_log_7280_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7281_neg : (100978629 / 1000000000) ≤ -Real.log (1000000 / 1106253) ∧
    -Real.log (1000000 / 1106253) ≤ (10097863 / 100000000) := by
  have h := checkLog_sound (w := (106253 / 2106253)) (n := 12)
    (lo := (100978629 / 1000000000)) (hi := (10097863 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1106253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1106253 / 1000000) = 1/(1000000 / 1106253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7281 : Bounds (100978629 / 1000000000) (10097863 / 100000000) (Real.log (1106253 / 1000000)) := by
  have h := reflection_log_7281_neg
  have he : Real.log (1106253 / 1000000) = -Real.log (1000000 / 1106253) := by
    rw [show ((1106253 / 1000000) : ℝ) = ((1000000 / 1106253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7282_neg : (112332541 / 1000000000) ≤ -Real.log (893747 / 1000000) ∧
    -Real.log (893747 / 1000000) ≤ (56166271 / 500000000) := by
  have h := checkLog_sound (w := (106253 / 1893747)) (n := 12)
    (lo := (112332541 / 1000000000)) (hi := (56166271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 893747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 893747) = 1/(893747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7282 : Bounds (-56166271 / 500000000) (-112332541 / 1000000000) (Real.log (893747 / 1000000)) := by
  have h := reflection_log_7282_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7283_neg : (20280137 / 200000000) ≤ -Real.log (6250 / 6917) ∧
    -Real.log (6250 / 6917) ≤ (50700343 / 500000000) := by
  have h := checkLog_sound (w := (667 / 13167)) (n := 12)
    (lo := (20280137 / 200000000)) (hi := (50700343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6917 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6917 / 6250) = 1/(6250 / 6917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7283 : Bounds (20280137 / 200000000) (50700343 / 500000000) (Real.log (6917 / 6250)) := by
  have h := reflection_log_7283_neg
  have he : Real.log (6917 / 6250) = -Real.log (6250 / 6917) := by
    rw [show ((6917 / 6250) : ℝ) = ((6250 / 6917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7284_neg : (112855197 / 1000000000) ≤ -Real.log (5583 / 6250) ∧
    -Real.log (5583 / 6250) ≤ (56427599 / 500000000) := by
  have h := checkLog_sound (w := (667 / 11833)) (n := 12)
    (lo := (112855197 / 1000000000)) (hi := (56427599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 5583) = 1/(5583 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7284 : Bounds (-56427599 / 500000000) (-112855197 / 1000000000) (Real.log (5583 / 6250)) := by
  have h := reflection_log_7284_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7285_neg : (11454511 / 1000000000) ≤ -Real.log (38617611 / 39062500) ∧
    -Real.log (38617611 / 39062500) ≤ (715907 / 62500000) := by
  have h := checkLog_sound (w := (444889 / 77680111)) (n := 12)
    (lo := (11454511 / 1000000000)) (hi := (715907 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 38617611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 38617611) = 1/(38617611 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7285 : Bounds (-715907 / 62500000) (-11454511 / 1000000000) (Real.log (38617611 / 39062500)) := by
  have h := reflection_log_7285_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7286_neg : (1419239 / 125000000) ≤ -Real.log (988710299991 / 1000000000000) ∧
    -Real.log (988710299991 / 1000000000000) ≤ (11353913 / 1000000000) := by
  have h := checkLog_sound (w := (11289700009 / 1988710299991)) (n := 12)
    (lo := (1419239 / 125000000)) (hi := (11353913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988710299991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988710299991) = 1/(988710299991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7286 : Bounds (-11353913 / 1000000000) (-1419239 / 125000000) (Real.log (988710299991 / 1000000000000)) := by
  have h := reflection_log_7286_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7287_neg : (21331117 / 100000000) ≤ -Real.log (250000000000 / 309442437289) ∧
    -Real.log (250000000000 / 309442437289) ≤ (213311171 / 1000000000) := by
  have h := checkLog_sound (w := (59442437289 / 559442437289)) (n := 12)
    (lo := (21331117 / 100000000)) (hi := (213311171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309442437289 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309442437289 / 250000000000) = 1/(250000000000 / 309442437289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7287 : Bounds (21331117 / 100000000) (213311171 / 1000000000) (Real.log (309442437289 / 250000000000)) := by
  have h := reflection_log_7287_neg
  have he : Real.log (309442437289 / 250000000000) = -Real.log (250000000000 / 309442437289) := by
    rw [show ((309442437289 / 250000000000) : ℝ) = ((250000000000 / 309442437289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7288_neg : (214255883 / 1000000000) ≤ -Real.log (250000000000 / 309734909547) ∧
    -Real.log (250000000000 / 309734909547) ≤ (53563971 / 250000000) := by
  have h := checkLog_sound (w := (59734909547 / 559734909547)) (n := 12)
    (lo := (214255883 / 1000000000)) (hi := (53563971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309734909547 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309734909547 / 250000000000) = 1/(250000000000 / 309734909547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7288 : Bounds (214255883 / 1000000000) (53563971 / 250000000) (Real.log (309734909547 / 250000000000)) := by
  have h := reflection_log_7288_neg
  have he : Real.log (309734909547 / 250000000000) = -Real.log (250000000000 / 309734909547) := by
    rw [show ((309734909547 / 250000000000) : ℝ) = ((250000000000 / 309734909547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7289_neg : (214217711 / 500000000) ≤ -Real.log (25000000000 / 38371356147) ∧
    -Real.log (25000000000 / 38371356147) ≤ (428435423 / 1000000000) := by
  have h := checkLog_sound (w := (13371356147 / 63371356147)) (n := 12)
    (lo := (214217711 / 500000000)) (hi := (428435423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38371356147 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38371356147 / 25000000000) = 1/(25000000000 / 38371356147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7289 : Bounds (214217711 / 500000000) (428435423 / 1000000000) (Real.log (38371356147 / 25000000000)) := by
  have h := reflection_log_7289_neg
  have he : Real.log (38371356147 / 25000000000) = -Real.log (25000000000 / 38371356147) := by
    rw [show ((38371356147 / 25000000000) : ℝ) = ((25000000000 / 38371356147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7290_neg : (429482133 / 1000000000) ≤ -Real.log (500000000000 / 768230818009) ∧
    -Real.log (500000000000 / 768230818009) ≤ (214741067 / 500000000) := by
  have h := checkLog_sound (w := (268230818009 / 1268230818009)) (n := 12)
    (lo := (429482133 / 1000000000)) (hi := (214741067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768230818009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768230818009 / 500000000000) = 1/(500000000000 / 768230818009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7290 : Bounds (429482133 / 1000000000) (214741067 / 500000000) (Real.log (768230818009 / 500000000000)) := by
  have h := reflection_log_7290_neg
  have he : Real.log (768230818009 / 500000000000) = -Real.log (500000000000 / 768230818009) := by
    rw [show ((768230818009 / 500000000000) : ℝ) = ((500000000000 / 768230818009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7291_neg : (192271887 / 1000000000) ≤ -Real.log (250 / 303) ∧
    -Real.log (250 / 303) ≤ (12016993 / 62500000) := by
  have h := checkLog_sound (w := (53 / 553)) (n := 12)
    (lo := (192271887 / 1000000000)) (hi := (12016993 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303 / 250) = 1/(250 / 303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7291 : Bounds (192271887 / 1000000000) (12016993 / 62500000) (Real.log (303 / 250)) := by
  have h := reflection_log_7291_neg
  have he : Real.log (303 / 250) = -Real.log (250 / 303) := by
    rw [show ((303 / 250) : ℝ) = ((250 / 303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7292_neg : (238257189 / 1000000000) ≤ -Real.log (197 / 250) ∧
    -Real.log (197 / 250) ≤ (23825719 / 100000000) := by
  have h := checkLog_sound (w := (53 / 447)) (n := 12)
    (lo := (238257189 / 1000000000)) (hi := (23825719 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 197) = 1/(197 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7292 : Bounds (-23825719 / 100000000) (-238257189 / 1000000000) (Real.log (197 / 250)) := by
  have h := reflection_log_7292_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7293_neg : (211977 / 1000000000) ≤ -Real.log (250000 / 250053) ∧
    -Real.log (250000 / 250053) ≤ (105989 / 500000000) := by
  have h := checkLog_sound (w := (53 / 500053)) (n := 12)
    (lo := (211977 / 1000000000)) (hi := (105989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250053 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250053 / 250000) = 1/(250000 / 250053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7293 : Bounds (211977 / 1000000000) (105989 / 500000000) (Real.log (250053 / 250000)) := by
  have h := reflection_log_7293_neg
  have he : Real.log (250053 / 250000) = -Real.log (250000 / 250053) := by
    rw [show ((250053 / 250000) : ℝ) = ((250000 / 250053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7294_neg : (106011 / 500000000) ≤ -Real.log (249947 / 250000) ∧
    -Real.log (249947 / 250000) ≤ (212023 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 499947)) (n := 12)
    (lo := (106011 / 500000000)) (hi := (212023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249947) = 1/(249947 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7294 : Bounds (-212023 / 1000000000) (-106011 / 500000000) (Real.log (249947 / 250000)) := by
  have h := reflection_log_7294_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7295_neg : (50605007 / 500000000) ≤ -Real.log (1000000 / 1106509) ∧
    -Real.log (1000000 / 1106509) ≤ (20242003 / 200000000) := by
  have h := checkLog_sound (w := (106509 / 2106509)) (n := 12)
    (lo := (50605007 / 500000000)) (hi := (20242003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1106509 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1106509 / 1000000) = 1/(1000000 / 1106509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7295 : Bounds (50605007 / 500000000) (20242003 / 200000000) (Real.log (1106509 / 1000000)) := by
  have h := reflection_log_7295_neg
  have he : Real.log (1106509 / 1000000) = -Real.log (1000000 / 1106509) := by
    rw [show ((1106509 / 1000000) : ℝ) = ((1000000 / 1106509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
