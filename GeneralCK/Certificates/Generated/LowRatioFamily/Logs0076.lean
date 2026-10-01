import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4864_neg : (8718357 / 1000000000) ≤ -Real.log (991319537439 / 1000000000000) ∧
    -Real.log (991319537439 / 1000000000000) ≤ (4359179 / 500000000) := by
  have h := checkLog_sound (w := (8680462561 / 1991319537439)) (n := 12)
    (lo := (8718357 / 1000000000)) (hi := (4359179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991319537439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991319537439) = 1/(991319537439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4864 : Bounds (-4359179 / 500000000) (-8718357 / 1000000000) (Real.log (991319537439 / 1000000000000)) := by
  have h := reflection_log_4864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4865_neg : (8674053 / 1000000000) ≤ -Real.log (991363457511 / 1000000000000) ∧
    -Real.log (991363457511 / 1000000000000) ≤ (4337027 / 500000000) := by
  have h := checkLog_sound (w := (8636542489 / 1991363457511)) (n := 12)
    (lo := (8674053 / 1000000000)) (hi := (4337027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991363457511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991363457511) = 1/(991363457511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4865 : Bounds (-4337027 / 500000000) (-8674053 / 1000000000) (Real.log (991363457511 / 1000000000000)) := by
  have h := reflection_log_4865_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4866_neg : (186403869 / 1000000000) ≤ -Real.log (500000000000 / 602454394217) ∧
    -Real.log (500000000000 / 602454394217) ≤ (18640387 / 100000000) := by
  have h := checkLog_sound (w := (102454394217 / 1102454394217)) (n := 12)
    (lo := (186403869 / 1000000000)) (hi := (18640387 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602454394217 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602454394217 / 500000000000) = 1/(500000000000 / 602454394217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4866 : Bounds (186403869 / 1000000000) (18640387 / 100000000) (Real.log (602454394217 / 500000000000)) := by
  have h := reflection_log_4866_neg
  have he : Real.log (602454394217 / 500000000000) = -Real.log (500000000000 / 602454394217) := by
    rw [show ((602454394217 / 500000000000) : ℝ) = ((500000000000 / 602454394217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4867_neg : (23359999 / 125000000) ≤ -Real.log (50000000000 / 60274130461) ∧
    -Real.log (50000000000 / 60274130461) ≤ (186879993 / 1000000000) := by
  have h := checkLog_sound (w := (10274130461 / 110274130461)) (n := 12)
    (lo := (23359999 / 125000000)) (hi := (186879993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60274130461 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60274130461 / 50000000000) = 1/(50000000000 / 60274130461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4867 : Bounds (23359999 / 125000000) (186879993 / 1000000000) (Real.log (60274130461 / 50000000000)) := by
  have h := reflection_log_4867_neg
  have he : Real.log (60274130461 / 50000000000) = -Real.log (50000000000 / 60274130461) := by
    rw [show ((60274130461 / 50000000000) : ℝ) = ((50000000000 / 60274130461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4868_neg : (46762857 / 125000000) ≤ -Real.log (250000000000 / 363421666053) ∧
    -Real.log (250000000000 / 363421666053) ≤ (374102857 / 1000000000) := by
  have h := checkLog_sound (w := (113421666053 / 613421666053)) (n := 12)
    (lo := (46762857 / 125000000)) (hi := (374102857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363421666053 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363421666053 / 250000000000) = 1/(250000000000 / 363421666053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4868 : Bounds (46762857 / 125000000) (374102857 / 1000000000) (Real.log (363421666053 / 250000000000)) := by
  have h := reflection_log_4868_neg
  have he : Real.log (363421666053 / 250000000000) = -Real.log (250000000000 / 363421666053) := by
    rw [show ((363421666053 / 250000000000) : ℝ) = ((250000000000 / 363421666053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4869_neg : (18715497 / 50000000) ≤ -Real.log (500000000000 / 726993865031) ∧
    -Real.log (500000000000 / 726993865031) ≤ (374309941 / 1000000000) := by
  have h := checkLog_sound (w := (226993865031 / 1226993865031)) (n := 12)
    (lo := (18715497 / 50000000)) (hi := (374309941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726993865031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726993865031 / 500000000000) = 1/(500000000000 / 726993865031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4869 : Bounds (18715497 / 50000000) (374309941 / 1000000000) (Real.log (726993865031 / 500000000000)) := by
  have h := reflection_log_4869_neg
  have he : Real.log (726993865031 / 500000000000) = -Real.log (500000000000 / 726993865031) := by
    rw [show ((726993865031 / 500000000000) : ℝ) = ((500000000000 / 726993865031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4870_neg : (169827159 / 1000000000) ≤ -Real.log (10000 / 11851) ∧
    -Real.log (10000 / 11851) ≤ (4245679 / 25000000) := by
  have h := checkLog_sound (w := (1851 / 21851)) (n := 12)
    (lo := (169827159 / 1000000000)) (hi := (4245679 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11851 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11851 / 10000) = 1/(10000 / 11851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4870 : Bounds (169827159 / 1000000000) (4245679 / 25000000) (Real.log (11851 / 10000)) := by
  have h := reflection_log_4870_neg
  have he : Real.log (11851 / 10000) = -Real.log (10000 / 11851) := by
    rw [show ((11851 / 10000) : ℝ) = ((10000 / 11851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4871_neg : (12793117 / 62500000) ≤ -Real.log (8149 / 10000) ∧
    -Real.log (8149 / 10000) ≤ (204689873 / 1000000000) := by
  have h := checkLog_sound (w := (1851 / 18149)) (n := 12)
    (lo := (12793117 / 62500000)) (hi := (204689873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8149) = 1/(8149 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4871 : Bounds (-204689873 / 1000000000) (-12793117 / 62500000) (Real.log (8149 / 10000)) := by
  have h := reflection_log_4871_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4872_neg : (92541 / 500000000) ≤ -Real.log (10000000 / 10001851) ∧
    -Real.log (10000000 / 10001851) ≤ (185083 / 1000000000) := by
  have h := checkLog_sound (w := (1851 / 20001851)) (n := 12)
    (lo := (92541 / 500000000)) (hi := (185083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001851 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001851 / 10000000) = 1/(10000000 / 10001851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4872 : Bounds (92541 / 500000000) (185083 / 1000000000) (Real.log (10001851 / 10000000)) := by
  have h := reflection_log_4872_neg
  have he : Real.log (10001851 / 10000000) = -Real.log (10000000 / 10001851) := by
    rw [show ((10001851 / 10000000) : ℝ) = ((10000000 / 10001851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4873_neg : (185117 / 1000000000) ≤ -Real.log (9998149 / 10000000) ∧
    -Real.log (9998149 / 10000000) ≤ (92559 / 500000000) := by
  have h := checkLog_sound (w := (1851 / 19998149)) (n := 12)
    (lo := (185117 / 1000000000)) (hi := (92559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998149) = 1/(9998149 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4873 : Bounds (-92559 / 500000000) (-185117 / 1000000000) (Real.log (9998149 / 10000000)) := by
  have h := reflection_log_4873_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4874_neg : (8891157 / 100000000) ≤ -Real.log (125000 / 136623) ∧
    -Real.log (125000 / 136623) ≤ (88911571 / 1000000000) := by
  have h := checkLog_sound (w := (11623 / 261623)) (n := 12)
    (lo := (8891157 / 100000000)) (hi := (88911571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136623 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136623 / 125000) = 1/(125000 / 136623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4874 : Bounds (8891157 / 100000000) (88911571 / 1000000000) (Real.log (136623 / 125000)) := by
  have h := reflection_log_4874_neg
  have he : Real.log (136623 / 125000) = -Real.log (125000 / 136623) := by
    rw [show ((136623 / 125000) : ℝ) = ((125000 / 136623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4875_neg : (24398797 / 250000000) ≤ -Real.log (113377 / 125000) ∧
    -Real.log (113377 / 125000) ≤ (97595189 / 1000000000) := by
  have h := checkLog_sound (w := (11623 / 238377)) (n := 12)
    (lo := (24398797 / 250000000)) (hi := (97595189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113377) = 1/(113377 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4875 : Bounds (-97595189 / 1000000000) (-24398797 / 250000000) (Real.log (113377 / 125000)) := by
  have h := reflection_log_4875_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4876_neg : (89127469 / 1000000000) ≤ -Real.log (50000 / 54661) ∧
    -Real.log (50000 / 54661) ≤ (8912747 / 100000000) := by
  have h := checkLog_sound (w := (4661 / 104661)) (n := 12)
    (lo := (89127469 / 1000000000)) (hi := (8912747 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54661 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54661 / 50000) = 1/(50000 / 54661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4876 : Bounds (89127469 / 1000000000) (8912747 / 100000000) (Real.log (54661 / 50000)) := by
  have h := reflection_log_4876_neg
  have he : Real.log (54661 / 50000) = -Real.log (50000 / 54661) := by
    rw [show ((54661 / 50000) : ℝ) = ((50000 / 54661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4877_neg : (12231927 / 125000000) ≤ -Real.log (45339 / 50000) ∧
    -Real.log (45339 / 50000) ≤ (97855417 / 1000000000) := by
  have h := checkLog_sound (w := (4661 / 95339)) (n := 12)
    (lo := (12231927 / 125000000)) (hi := (97855417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45339) = 1/(45339 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4877 : Bounds (-97855417 / 1000000000) (-12231927 / 125000000) (Real.log (45339 / 50000)) := by
  have h := reflection_log_4877_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4878_neg : (4363973 / 500000000) ≤ -Real.log (2478275079 / 2500000000) ∧
    -Real.log (2478275079 / 2500000000) ≤ (8727947 / 1000000000) := by
  have h := checkLog_sound (w := (21724921 / 4978275079)) (n := 12)
    (lo := (4363973 / 500000000)) (hi := (8727947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2478275079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2478275079) = 1/(2478275079 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4878 : Bounds (-8727947 / 1000000000) (-4363973 / 500000000) (Real.log (2478275079 / 2500000000)) := by
  have h := reflection_log_4878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4879_neg : (8683617 / 1000000000) ≤ -Real.log (15489905871 / 15625000000) ∧
    -Real.log (15489905871 / 15625000000) ≤ (4341809 / 500000000) := by
  have h := checkLog_sound (w := (135094129 / 31114905871)) (n := 12)
    (lo := (8683617 / 1000000000)) (hi := (4341809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15489905871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15489905871) = 1/(15489905871 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4879 : Bounds (-4341809 / 500000000) (-8683617 / 1000000000) (Real.log (15489905871 / 15625000000)) := by
  have h := reflection_log_4879_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4880_neg : (93253379 / 500000000) ≤ -Real.log (500000000000 / 602516383393) ∧
    -Real.log (500000000000 / 602516383393) ≤ (186506759 / 1000000000) := by
  have h := checkLog_sound (w := (102516383393 / 1102516383393)) (n := 12)
    (lo := (93253379 / 500000000)) (hi := (186506759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602516383393 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602516383393 / 500000000000) = 1/(500000000000 / 602516383393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4880 : Bounds (93253379 / 500000000) (186506759 / 1000000000) (Real.log (602516383393 / 500000000000)) := by
  have h := reflection_log_4880_neg
  have he : Real.log (602516383393 / 500000000000) = -Real.log (500000000000 / 602516383393) := by
    rw [show ((602516383393 / 500000000000) : ℝ) = ((500000000000 / 602516383393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4881_neg : (37396577 / 200000000) ≤ -Real.log (100000000000 / 120560665211) ∧
    -Real.log (100000000000 / 120560665211) ≤ (93491443 / 500000000) := by
  have h := checkLog_sound (w := (20560665211 / 220560665211)) (n := 12)
    (lo := (37396577 / 200000000)) (hi := (93491443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120560665211 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120560665211 / 100000000000) = 1/(100000000000 / 120560665211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4881 : Bounds (37396577 / 200000000) (93491443 / 500000000) (Real.log (120560665211 / 100000000000)) := by
  have h := reflection_log_4881_neg
  have he : Real.log (120560665211 / 100000000000) = -Real.log (100000000000 / 120560665211) := by
    rw [show ((120560665211 / 100000000000) : ℝ) = ((100000000000 / 120560665211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4882_neg : (18715497 / 50000000) ≤ -Real.log (50000000000 / 72699386503) ∧
    -Real.log (50000000000 / 72699386503) ≤ (374309941 / 1000000000) := by
  have h := checkLog_sound (w := (22699386503 / 122699386503)) (n := 12)
    (lo := (18715497 / 50000000)) (hi := (374309941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72699386503 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72699386503 / 50000000000) = 1/(50000000000 / 72699386503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4882 : Bounds (18715497 / 50000000) (374309941 / 1000000000) (Real.log (72699386503 / 50000000000)) := by
  have h := reflection_log_4882_neg
  have he : Real.log (72699386503 / 50000000000) = -Real.log (50000000000 / 72699386503) := by
    rw [show ((72699386503 / 50000000000) : ℝ) = ((50000000000 / 72699386503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4883_neg : (374517031 / 1000000000) ≤ -Real.log (5000000000 / 7271444349) ∧
    -Real.log (5000000000 / 7271444349) ≤ (46814629 / 125000000) := by
  have h := checkLog_sound (w := (2271444349 / 12271444349)) (n := 12)
    (lo := (374517031 / 1000000000)) (hi := (46814629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7271444349 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7271444349 / 5000000000) = 1/(5000000000 / 7271444349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4883 : Bounds (374517031 / 1000000000) (46814629 / 125000000) (Real.log (7271444349 / 5000000000)) := by
  have h := reflection_log_4883_neg
  have he : Real.log (7271444349 / 5000000000) = -Real.log (5000000000 / 7271444349) := by
    rw [show ((7271444349 / 5000000000) : ℝ) = ((5000000000 / 7271444349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4884_neg : (10619471 / 62500000) ≤ -Real.log (2500 / 2963) ∧
    -Real.log (2500 / 2963) ≤ (169911537 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 5463)) (n := 12)
    (lo := (10619471 / 62500000)) (hi := (169911537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2963 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2963 / 2500) = 1/(2500 / 2963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4884 : Bounds (10619471 / 62500000) (169911537 / 1000000000) (Real.log (2963 / 2500)) := by
  have h := reflection_log_4884_neg
  have he : Real.log (2963 / 2500) = -Real.log (2500 / 2963) := by
    rw [show ((2963 / 2500) : ℝ) = ((2500 / 2963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4885_neg : (102406297 / 500000000) ≤ -Real.log (2037 / 2500) ∧
    -Real.log (2037 / 2500) ≤ (40962519 / 200000000) := by
  have h := checkLog_sound (w := (463 / 4537)) (n := 12)
    (lo := (102406297 / 500000000)) (hi := (40962519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2037) = 1/(2037 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4885 : Bounds (-40962519 / 200000000) (-102406297 / 500000000) (Real.log (2037 / 2500)) := by
  have h := reflection_log_4885_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4886_neg : (92591 / 500000000) ≤ -Real.log (2500000 / 2500463) ∧
    -Real.log (2500000 / 2500463) ≤ (185183 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 5000463)) (n := 12)
    (lo := (92591 / 500000000)) (hi := (185183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500463 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500463 / 2500000) = 1/(2500000 / 2500463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4886 : Bounds (92591 / 500000000) (185183 / 1000000000) (Real.log (2500463 / 2500000)) := by
  have h := reflection_log_4886_neg
  have he : Real.log (2500463 / 2500000) = -Real.log (2500000 / 2500463) := by
    rw [show ((2500463 / 2500000) : ℝ) = ((2500000 / 2500463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4887_neg : (185217 / 1000000000) ≤ -Real.log (2499537 / 2500000) ∧
    -Real.log (2499537 / 2500000) ≤ (92609 / 500000000) := by
  have h := checkLog_sound (w := (463 / 4999537)) (n := 12)
    (lo := (185217 / 1000000000)) (hi := (92609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499537) = 1/(2499537 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4887 : Bounds (-92609 / 500000000) (-185217 / 1000000000) (Real.log (2499537 / 2500000)) := by
  have h := reflection_log_4887_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4888_neg : (8895823 / 100000000) ≤ -Real.log (200000 / 218607) ∧
    -Real.log (200000 / 218607) ≤ (88958231 / 1000000000) := by
  have h := checkLog_sound (w := (18607 / 418607)) (n := 12)
    (lo := (8895823 / 100000000)) (hi := (88958231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218607 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218607 / 200000) = 1/(200000 / 218607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4888 : Bounds (8895823 / 100000000) (88958231 / 1000000000) (Real.log (218607 / 200000)) := by
  have h := reflection_log_4888_neg
  have he : Real.log (218607 / 200000) = -Real.log (200000 / 218607) := by
    rw [show ((218607 / 200000) : ℝ) = ((200000 / 218607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4889_neg : (48825709 / 500000000) ≤ -Real.log (181393 / 200000) ∧
    -Real.log (181393 / 200000) ≤ (97651419 / 1000000000) := by
  have h := checkLog_sound (w := (18607 / 381393)) (n := 12)
    (lo := (48825709 / 500000000)) (hi := (97651419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181393) = 1/(181393 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4889 : Bounds (-97651419 / 1000000000) (-48825709 / 500000000) (Real.log (181393 / 200000)) := by
  have h := reflection_log_4889_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4890_neg : (89174119 / 1000000000) ≤ -Real.log (1000000 / 1093271) ∧
    -Real.log (1000000 / 1093271) ≤ (2229353 / 25000000) := by
  have h := checkLog_sound (w := (93271 / 2093271)) (n := 12)
    (lo := (89174119 / 1000000000)) (hi := (2229353 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093271 / 1000000) = 1/(1000000 / 1093271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4890 : Bounds (89174119 / 1000000000) (2229353 / 25000000) (Real.log (1093271 / 1000000)) := by
  have h := reflection_log_4890_neg
  have he : Real.log (1093271 / 1000000) = -Real.log (1000000 / 1093271) := by
    rw [show ((1093271 / 1000000) : ℝ) = ((1000000 / 1093271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4891_neg : (4895583 / 50000000) ≤ -Real.log (906729 / 1000000) ∧
    -Real.log (906729 / 1000000) ≤ (97911661 / 1000000000) := by
  have h := checkLog_sound (w := (93271 / 1906729)) (n := 12)
    (lo := (4895583 / 50000000)) (hi := (97911661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906729) = 1/(906729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4891 : Bounds (-97911661 / 1000000000) (-4895583 / 50000000) (Real.log (906729 / 1000000)) := by
  have h := reflection_log_4891_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4892_neg : (436877 / 50000000) ≤ -Real.log (991300520559 / 1000000000000) ∧
    -Real.log (991300520559 / 1000000000000) ≤ (8737541 / 1000000000) := by
  have h := checkLog_sound (w := (8699479441 / 1991300520559)) (n := 12)
    (lo := (436877 / 50000000)) (hi := (8737541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991300520559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991300520559) = 1/(991300520559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4892 : Bounds (-8737541 / 1000000000) (-436877 / 50000000) (Real.log (991300520559 / 1000000000000)) := by
  have h := reflection_log_4892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4893_neg : (8693187 / 1000000000) ≤ -Real.log (39653779551 / 40000000000) ∧
    -Real.log (39653779551 / 40000000000) ≤ (2173297 / 250000000) := by
  have h := checkLog_sound (w := (346220449 / 79653779551)) (n := 12)
    (lo := (8693187 / 1000000000)) (hi := (2173297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39653779551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39653779551) = 1/(39653779551 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4893 : Bounds (-2173297 / 250000000) (-8693187 / 1000000000) (Real.log (39653779551 / 40000000000)) := by
  have h := reflection_log_4893_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4894_neg : (186609649 / 1000000000) ≤ -Real.log (25000000000 / 30128918977) ∧
    -Real.log (25000000000 / 30128918977) ≤ (3732193 / 20000000) := by
  have h := checkLog_sound (w := (5128918977 / 55128918977)) (n := 12)
    (lo := (186609649 / 1000000000)) (hi := (3732193 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30128918977 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30128918977 / 25000000000) = 1/(25000000000 / 30128918977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4894 : Bounds (186609649 / 1000000000) (3732193 / 20000000) (Real.log (30128918977 / 25000000000)) := by
  have h := reflection_log_4894_neg
  have he : Real.log (30128918977 / 25000000000) = -Real.log (25000000000 / 30128918977) := by
    rw [show ((30128918977 / 25000000000) : ℝ) = ((25000000000 / 30128918977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4895_neg : (9354289 / 50000000) ≤ -Real.log (250000000000 / 301432677239) ∧
    -Real.log (250000000000 / 301432677239) ≤ (187085781 / 1000000000) := by
  have h := checkLog_sound (w := (51432677239 / 551432677239)) (n := 12)
    (lo := (9354289 / 50000000)) (hi := (187085781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301432677239 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301432677239 / 250000000000) = 1/(250000000000 / 301432677239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4895 : Bounds (9354289 / 50000000) (187085781 / 1000000000) (Real.log (301432677239 / 250000000000)) := by
  have h := reflection_log_4895_neg
  have he : Real.log (301432677239 / 250000000000) = -Real.log (250000000000 / 301432677239) := by
    rw [show ((301432677239 / 250000000000) : ℝ) = ((250000000000 / 301432677239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4896_neg : (374517031 / 1000000000) ≤ -Real.log (500000000000 / 727144434899) ∧
    -Real.log (500000000000 / 727144434899) ≤ (46814629 / 125000000) := by
  have h := checkLog_sound (w := (227144434899 / 1227144434899)) (n := 12)
    (lo := (374517031 / 1000000000)) (hi := (46814629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727144434899 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727144434899 / 500000000000) = 1/(500000000000 / 727144434899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4896 : Bounds (374517031 / 1000000000) (46814629 / 125000000) (Real.log (727144434899 / 500000000000)) := by
  have h := reflection_log_4896_neg
  have he : Real.log (727144434899 / 500000000000) = -Real.log (500000000000 / 727144434899) := by
    rw [show ((727144434899 / 500000000000) : ℝ) = ((500000000000 / 727144434899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4897_neg : (374724131 / 1000000000) ≤ -Real.log (500000000000 / 727295041729) ∧
    -Real.log (500000000000 / 727295041729) ≤ (93681033 / 250000000) := by
  have h := checkLog_sound (w := (227295041729 / 1227295041729)) (n := 12)
    (lo := (374724131 / 1000000000)) (hi := (93681033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727295041729 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727295041729 / 500000000000) = 1/(500000000000 / 727295041729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4897 : Bounds (374724131 / 1000000000) (93681033 / 250000000) (Real.log (727295041729 / 500000000000)) := by
  have h := reflection_log_4897_neg
  have he : Real.log (727295041729 / 500000000000) = -Real.log (500000000000 / 727295041729) := by
    rw [show ((727295041729 / 500000000000) : ℝ) = ((500000000000 / 727295041729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4898_neg : (169995907 / 1000000000) ≤ -Real.log (10000 / 11853) ∧
    -Real.log (10000 / 11853) ≤ (42498977 / 250000000) := by
  have h := checkLog_sound (w := (1853 / 21853)) (n := 12)
    (lo := (169995907 / 1000000000)) (hi := (42498977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11853 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11853 / 10000) = 1/(10000 / 11853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4898 : Bounds (169995907 / 1000000000) (42498977 / 250000000) (Real.log (11853 / 10000)) := by
  have h := reflection_log_4898_neg
  have he : Real.log (11853 / 10000) = -Real.log (10000 / 11853) := by
    rw [show ((11853 / 10000) : ℝ) = ((10000 / 11853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4899_neg : (204935331 / 1000000000) ≤ -Real.log (8147 / 10000) ∧
    -Real.log (8147 / 10000) ≤ (51233833 / 250000000) := by
  have h := checkLog_sound (w := (1853 / 18147)) (n := 12)
    (lo := (204935331 / 1000000000)) (hi := (51233833 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8147) = 1/(8147 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4899 : Bounds (-51233833 / 250000000) (-204935331 / 1000000000) (Real.log (8147 / 10000)) := by
  have h := reflection_log_4899_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4900_neg : (92641 / 500000000) ≤ -Real.log (10000000 / 10001853) ∧
    -Real.log (10000000 / 10001853) ≤ (185283 / 1000000000) := by
  have h := checkLog_sound (w := (1853 / 20001853)) (n := 12)
    (lo := (92641 / 500000000)) (hi := (185283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001853 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001853 / 10000000) = 1/(10000000 / 10001853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4900 : Bounds (92641 / 500000000) (185283 / 1000000000) (Real.log (10001853 / 10000000)) := by
  have h := reflection_log_4900_neg
  have he : Real.log (10001853 / 10000000) = -Real.log (10000000 / 10001853) := by
    rw [show ((10001853 / 10000000) : ℝ) = ((10000000 / 10001853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4901_neg : (185317 / 1000000000) ≤ -Real.log (9998147 / 10000000) ∧
    -Real.log (9998147 / 10000000) ≤ (92659 / 500000000) := by
  have h := checkLog_sound (w := (1853 / 19998147)) (n := 12)
    (lo := (185317 / 1000000000)) (hi := (92659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998147) = 1/(9998147 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4901 : Bounds (-92659 / 500000000) (-185317 / 1000000000) (Real.log (9998147 / 10000000)) := by
  have h := reflection_log_4901_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4902_neg : (11125611 / 125000000) ≤ -Real.log (500000 / 546543) ∧
    -Real.log (500000 / 546543) ≤ (89004889 / 1000000000) := by
  have h := checkLog_sound (w := (46543 / 1046543)) (n := 12)
    (lo := (11125611 / 125000000)) (hi := (89004889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546543 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546543 / 500000) = 1/(500000 / 546543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4902 : Bounds (11125611 / 125000000) (89004889 / 1000000000) (Real.log (546543 / 500000)) := by
  have h := reflection_log_4902_neg
  have he : Real.log (546543 / 500000) = -Real.log (500000 / 546543) := by
    rw [show ((546543 / 500000) : ℝ) = ((500000 / 546543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4903_neg : (97707651 / 1000000000) ≤ -Real.log (453457 / 500000) ∧
    -Real.log (453457 / 500000) ≤ (24426913 / 250000000) := by
  have h := checkLog_sound (w := (46543 / 953457)) (n := 12)
    (lo := (97707651 / 1000000000)) (hi := (24426913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453457) = 1/(453457 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4903 : Bounds (-24426913 / 250000000) (-97707651 / 1000000000) (Real.log (453457 / 500000)) := by
  have h := reflection_log_4903_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4904_neg : (89220767 / 1000000000) ≤ -Real.log (500000 / 546661) ∧
    -Real.log (500000 / 546661) ≤ (2788149 / 31250000) := by
  have h := checkLog_sound (w := (46661 / 1046661)) (n := 12)
    (lo := (89220767 / 1000000000)) (hi := (2788149 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546661 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546661 / 500000) = 1/(500000 / 546661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4904 : Bounds (89220767 / 1000000000) (2788149 / 31250000) (Real.log (546661 / 500000)) := by
  have h := reflection_log_4904_neg
  have he : Real.log (546661 / 500000) = -Real.log (500000 / 546661) := by
    rw [show ((546661 / 500000) : ℝ) = ((500000 / 546661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4905_neg : (24491977 / 250000000) ≤ -Real.log (453339 / 500000) ∧
    -Real.log (453339 / 500000) ≤ (97967909 / 1000000000) := by
  have h := checkLog_sound (w := (46661 / 953339)) (n := 12)
    (lo := (24491977 / 250000000)) (hi := (97967909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453339) = 1/(453339 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4905 : Bounds (-97967909 / 1000000000) (-24491977 / 250000000) (Real.log (453339 / 500000)) := by
  have h := reflection_log_4905_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4906_neg : (437357 / 50000000) ≤ -Real.log (247822751079 / 250000000000) ∧
    -Real.log (247822751079 / 250000000000) ≤ (8747141 / 1000000000) := by
  have h := checkLog_sound (w := (2177248921 / 497822751079)) (n := 12)
    (lo := (437357 / 50000000)) (hi := (8747141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247822751079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247822751079) = 1/(247822751079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4906 : Bounds (-8747141 / 1000000000) (-437357 / 50000000) (Real.log (247822751079 / 250000000000)) := by
  have h := reflection_log_4906_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4907_neg : (4351381 / 500000000) ≤ -Real.log (247833749151 / 250000000000) ∧
    -Real.log (247833749151 / 250000000000) ≤ (8702763 / 1000000000) := by
  have h := checkLog_sound (w := (2166250849 / 497833749151)) (n := 12)
    (lo := (4351381 / 500000000)) (hi := (8702763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247833749151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247833749151) = 1/(247833749151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4907 : Bounds (-8702763 / 1000000000) (-4351381 / 500000000) (Real.log (247833749151 / 250000000000)) := by
  have h := reflection_log_4907_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4908_neg : (9335627 / 50000000) ≤ -Real.log (25000000000 / 30132019133) ∧
    -Real.log (25000000000 / 30132019133) ≤ (186712541 / 1000000000) := by
  have h := checkLog_sound (w := (5132019133 / 55132019133)) (n := 12)
    (lo := (9335627 / 50000000)) (hi := (186712541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30132019133 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30132019133 / 25000000000) = 1/(25000000000 / 30132019133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4908 : Bounds (9335627 / 50000000) (186712541 / 1000000000) (Real.log (30132019133 / 25000000000)) := by
  have h := reflection_log_4908_neg
  have he : Real.log (30132019133 / 25000000000) = -Real.log (25000000000 / 30132019133) := by
    rw [show ((30132019133 / 25000000000) : ℝ) = ((25000000000 / 30132019133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4909_neg : (46797169 / 250000000) ≤ -Real.log (500000000000 / 602927389879) ∧
    -Real.log (500000000000 / 602927389879) ≤ (187188677 / 1000000000) := by
  have h := checkLog_sound (w := (102927389879 / 1102927389879)) (n := 12)
    (lo := (46797169 / 250000000)) (hi := (187188677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602927389879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602927389879 / 500000000000) = 1/(500000000000 / 602927389879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4909 : Bounds (46797169 / 250000000) (187188677 / 1000000000) (Real.log (602927389879 / 500000000000)) := by
  have h := reflection_log_4909_neg
  have he : Real.log (602927389879 / 500000000000) = -Real.log (500000000000 / 602927389879) := by
    rw [show ((602927389879 / 500000000000) : ℝ) = ((500000000000 / 602927389879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4910_neg : (374724131 / 1000000000) ≤ -Real.log (7812500000 / 11363985027) ∧
    -Real.log (7812500000 / 11363985027) ≤ (93681033 / 250000000) := by
  have h := checkLog_sound (w := (3551485027 / 19176485027)) (n := 12)
    (lo := (374724131 / 1000000000)) (hi := (93681033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11363985027 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11363985027 / 7812500000) = 1/(7812500000 / 11363985027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4910 : Bounds (374724131 / 1000000000) (93681033 / 250000000) (Real.log (11363985027 / 7812500000)) := by
  have h := reflection_log_4910_neg
  have he : Real.log (11363985027 / 7812500000) = -Real.log (7812500000 / 11363985027) := by
    rw [show ((11363985027 / 7812500000) : ℝ) = ((7812500000 / 11363985027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4911_neg : (187465619 / 500000000) ≤ -Real.log (500000000000 / 727445685529) ∧
    -Real.log (500000000000 / 727445685529) ≤ (374931239 / 1000000000) := by
  have h := checkLog_sound (w := (227445685529 / 1227445685529)) (n := 12)
    (lo := (187465619 / 500000000)) (hi := (374931239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727445685529 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727445685529 / 500000000000) = 1/(500000000000 / 727445685529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4911 : Bounds (187465619 / 500000000) (374931239 / 1000000000) (Real.log (727445685529 / 500000000000)) := by
  have h := reflection_log_4911_neg
  have he : Real.log (727445685529 / 500000000000) = -Real.log (500000000000 / 727445685529) := by
    rw [show ((727445685529 / 500000000000) : ℝ) = ((500000000000 / 727445685529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4912_neg : (17008027 / 100000000) ≤ -Real.log (5000 / 5927) ∧
    -Real.log (5000 / 5927) ≤ (170080271 / 1000000000) := by
  have h := checkLog_sound (w := (927 / 10927)) (n := 12)
    (lo := (17008027 / 100000000)) (hi := (170080271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5927 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5927 / 5000) = 1/(5000 / 5927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4912 : Bounds (17008027 / 100000000) (170080271 / 1000000000) (Real.log (5927 / 5000)) := by
  have h := reflection_log_4912_neg
  have he : Real.log (5927 / 5000) = -Real.log (5000 / 5927) := by
    rw [show ((5927 / 5000) : ℝ) = ((5000 / 5927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4913_neg : (205058083 / 1000000000) ≤ -Real.log (4073 / 5000) ∧
    -Real.log (4073 / 5000) ≤ (51264521 / 250000000) := by
  have h := checkLog_sound (w := (927 / 9073)) (n := 12)
    (lo := (205058083 / 1000000000)) (hi := (51264521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4073) = 1/(4073 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4913 : Bounds (-51264521 / 250000000) (-205058083 / 1000000000) (Real.log (4073 / 5000)) := by
  have h := reflection_log_4913_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4914_neg : (92691 / 500000000) ≤ -Real.log (5000000 / 5000927) ∧
    -Real.log (5000000 / 5000927) ≤ (185383 / 1000000000) := by
  have h := checkLog_sound (w := (927 / 10000927)) (n := 12)
    (lo := (92691 / 500000000)) (hi := (185383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000927 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000927 / 5000000) = 1/(5000000 / 5000927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4914 : Bounds (92691 / 500000000) (185383 / 1000000000) (Real.log (5000927 / 5000000)) := by
  have h := reflection_log_4914_neg
  have he : Real.log (5000927 / 5000000) = -Real.log (5000000 / 5000927) := by
    rw [show ((5000927 / 5000000) : ℝ) = ((5000000 / 5000927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4915_neg : (185417 / 1000000000) ≤ -Real.log (4999073 / 5000000) ∧
    -Real.log (4999073 / 5000000) ≤ (92709 / 500000000) := by
  have h := checkLog_sound (w := (927 / 9999073)) (n := 12)
    (lo := (185417 / 1000000000)) (hi := (92709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999073) = 1/(4999073 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4915 : Bounds (-92709 / 500000000) (-185417 / 1000000000) (Real.log (4999073 / 5000000)) := by
  have h := reflection_log_4915_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4916_neg : (11131443 / 125000000) ≤ -Real.log (1000000 / 1093137) ∧
    -Real.log (1000000 / 1093137) ≤ (17810309 / 200000000) := by
  have h := checkLog_sound (w := (93137 / 2093137)) (n := 12)
    (lo := (11131443 / 125000000)) (hi := (17810309 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093137 / 1000000) = 1/(1000000 / 1093137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4916 : Bounds (11131443 / 125000000) (17810309 / 200000000) (Real.log (1093137 / 1000000)) := by
  have h := reflection_log_4916_neg
  have he : Real.log (1093137 / 1000000) = -Real.log (1000000 / 1093137) := by
    rw [show ((1093137 / 1000000) : ℝ) = ((1000000 / 1093137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4917_neg : (97763887 / 1000000000) ≤ -Real.log (906863 / 1000000) ∧
    -Real.log (906863 / 1000000) ≤ (6110243 / 62500000) := by
  have h := checkLog_sound (w := (93137 / 1906863)) (n := 12)
    (lo := (97763887 / 1000000000)) (hi := (6110243 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906863) = 1/(906863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4917 : Bounds (-6110243 / 62500000) (-97763887 / 1000000000) (Real.log (906863 / 1000000)) := by
  have h := reflection_log_4917_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4918_neg : (89267413 / 1000000000) ≤ -Real.log (1000000 / 1093373) ∧
    -Real.log (1000000 / 1093373) ≤ (44633707 / 500000000) := by
  have h := checkLog_sound (w := (93373 / 2093373)) (n := 12)
    (lo := (89267413 / 1000000000)) (hi := (44633707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093373 / 1000000) = 1/(1000000 / 1093373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4918 : Bounds (89267413 / 1000000000) (44633707 / 500000000) (Real.log (1093373 / 1000000)) := by
  have h := reflection_log_4918_neg
  have he : Real.log (1093373 / 1000000) = -Real.log (1000000 / 1093373) := by
    rw [show ((1093373 / 1000000) : ℝ) = ((1000000 / 1093373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4919_neg : (98024159 / 1000000000) ≤ -Real.log (906627 / 1000000) ∧
    -Real.log (906627 / 1000000) ≤ (612651 / 6250000) := by
  have h := checkLog_sound (w := (93373 / 1906627)) (n := 12)
    (lo := (98024159 / 1000000000)) (hi := (612651 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906627) = 1/(906627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4919 : Bounds (-612651 / 6250000) (-98024159 / 1000000000) (Real.log (906627 / 1000000)) := by
  have h := reflection_log_4919_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4920_neg : (1751349 / 200000000) ≤ -Real.log (991281482871 / 1000000000000) ∧
    -Real.log (991281482871 / 1000000000000) ≤ (4378373 / 500000000) := by
  have h := checkLog_sound (w := (8718517129 / 1991281482871)) (n := 12)
    (lo := (1751349 / 200000000)) (hi := (4378373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991281482871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991281482871) = 1/(991281482871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4920 : Bounds (-4378373 / 500000000) (-1751349 / 200000000) (Real.log (991281482871 / 1000000000000)) := by
  have h := reflection_log_4920_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4921_neg : (8712343 / 1000000000) ≤ -Real.log (991325499231 / 1000000000000) ∧
    -Real.log (991325499231 / 1000000000000) ≤ (1089043 / 125000000) := by
  have h := checkLog_sound (w := (8674500769 / 1991325499231)) (n := 12)
    (lo := (8712343 / 1000000000)) (hi := (1089043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991325499231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991325499231) = 1/(991325499231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4921 : Bounds (-1089043 / 125000000) (-8712343 / 1000000000) (Real.log (991325499231 / 1000000000000)) := by
  have h := reflection_log_4921_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4922_neg : (23351929 / 125000000) ≤ -Real.log (500000000000 / 602702392753) ∧
    -Real.log (500000000000 / 602702392753) ≤ (186815433 / 1000000000) := by
  have h := checkLog_sound (w := (102702392753 / 1102702392753)) (n := 12)
    (lo := (23351929 / 125000000)) (hi := (186815433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602702392753 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602702392753 / 500000000000) = 1/(500000000000 / 602702392753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4922 : Bounds (23351929 / 125000000) (186815433 / 1000000000) (Real.log (602702392753 / 500000000000)) := by
  have h := reflection_log_4922_neg
  have he : Real.log (602702392753 / 500000000000) = -Real.log (500000000000 / 602702392753) := by
    rw [show ((602702392753 / 500000000000) : ℝ) = ((500000000000 / 602702392753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4923_neg : (46822893 / 250000000) ≤ -Real.log (500000000000 / 602989432259) ∧
    -Real.log (500000000000 / 602989432259) ≤ (187291573 / 1000000000) := by
  have h := checkLog_sound (w := (102989432259 / 1102989432259)) (n := 12)
    (lo := (46822893 / 250000000)) (hi := (187291573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602989432259 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602989432259 / 500000000000) = 1/(500000000000 / 602989432259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4923 : Bounds (46822893 / 250000000) (187291573 / 1000000000) (Real.log (602989432259 / 500000000000)) := by
  have h := reflection_log_4923_neg
  have he : Real.log (602989432259 / 500000000000) = -Real.log (500000000000 / 602989432259) := by
    rw [show ((602989432259 / 500000000000) : ℝ) = ((500000000000 / 602989432259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4924_neg : (187465619 / 500000000) ≤ -Real.log (62500000000 / 90930710691) ∧
    -Real.log (62500000000 / 90930710691) ≤ (374931239 / 1000000000) := by
  have h := checkLog_sound (w := (28430710691 / 153430710691)) (n := 12)
    (lo := (187465619 / 500000000)) (hi := (374931239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90930710691 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90930710691 / 62500000000) = 1/(62500000000 / 90930710691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4924 : Bounds (187465619 / 500000000) (374931239 / 1000000000) (Real.log (90930710691 / 62500000000)) := by
  have h := reflection_log_4924_neg
  have he : Real.log (90930710691 / 62500000000) = -Real.log (62500000000 / 90930710691) := by
    rw [show ((90930710691 / 62500000000) : ℝ) = ((62500000000 / 90930710691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4925_neg : (187569177 / 500000000) ≤ -Real.log (100000000000 / 145519273263) ∧
    -Real.log (100000000000 / 145519273263) ≤ (75027671 / 200000000) := by
  have h := checkLog_sound (w := (45519273263 / 245519273263)) (n := 12)
    (lo := (187569177 / 500000000)) (hi := (75027671 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145519273263 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145519273263 / 100000000000) = 1/(100000000000 / 145519273263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4925 : Bounds (187569177 / 500000000) (75027671 / 200000000) (Real.log (145519273263 / 100000000000)) := by
  have h := reflection_log_4925_neg
  have he : Real.log (145519273263 / 100000000000) = -Real.log (100000000000 / 145519273263) := by
    rw [show ((145519273263 / 100000000000) : ℝ) = ((100000000000 / 145519273263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4926_neg : (85082313 / 500000000) ≤ -Real.log (2000 / 2371) ∧
    -Real.log (2000 / 2371) ≤ (170164627 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 4371)) (n := 12)
    (lo := (85082313 / 500000000)) (hi := (170164627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2371 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2371 / 2000) = 1/(2000 / 2371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4926 : Bounds (85082313 / 500000000) (170164627 / 1000000000) (Real.log (2371 / 2000)) := by
  have h := reflection_log_4926_neg
  have he : Real.log (2371 / 2000) = -Real.log (2000 / 2371) := by
    rw [show ((2371 / 2000) : ℝ) = ((2000 / 2371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4927_neg : (4103617 / 20000000) ≤ -Real.log (1629 / 2000) ∧
    -Real.log (1629 / 2000) ≤ (205180851 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 3629)) (n := 12)
    (lo := (4103617 / 20000000)) (hi := (205180851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1629) = 1/(1629 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4927 : Bounds (-205180851 / 1000000000) (-4103617 / 20000000) (Real.log (1629 / 2000)) := by
  have h := reflection_log_4927_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
