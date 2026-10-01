import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0460
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

theorem reflection_log_1_neg : (185733697 / 1000000000) ≤ -Real.log (1024 / 1233) ∧
    -Real.log (1024 / 1233) ≤ (92866849 / 500000000) := by
  have h := checkLog_sound (w := (209 / 2257)) (n := 12)
    (lo := (185733697 / 1000000000)) (hi := (92866849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233 / 1024) = 1/(1024 / 1233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (185733697 / 1000000000) (92866849 / 500000000) (Real.log (1233 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1233 / 1024) = -Real.log (1024 / 1233) := by
    rw [show ((1233 / 1024) : ℝ) = ((1024 / 1233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (57070923 / 250000000) ≤ -Real.log (815 / 1024) ∧
    -Real.log (815 / 1024) ≤ (228283693 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1839)) (n := 12)
    (lo := (57070923 / 250000000)) (hi := (228283693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 815) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 815) = 1/(815 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-228283693 / 1000000000) (-57070923 / 250000000) (Real.log (815 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (92745179 / 500000000) ≤ -Real.log (10240 / 12327) ∧
    -Real.log (10240 / 12327) ≤ (185490359 / 1000000000) := by
  have h := checkLog_sound (w := (2087 / 22567)) (n := 12)
    (lo := (92745179 / 500000000)) (hi := (185490359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12327 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12327 / 10240) = 1/(10240 / 12327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (92745179 / 500000000) (185490359 / 1000000000) (Real.log (12327 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12327 / 10240) = -Real.log (10240 / 12327) := by
    rw [show ((12327 / 10240) : ℝ) = ((10240 / 12327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (227915661 / 1000000000) ≤ -Real.log (8153 / 10240) ∧
    -Real.log (8153 / 10240) ≤ (113957831 / 500000000) := by
  have h := checkLog_sound (w := (2087 / 18393)) (n := 12)
    (lo := (227915661 / 1000000000)) (hi := (113957831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8153) = 1/(8153 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-113957831 / 500000000) (-227915661 / 1000000000) (Real.log (8153 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (21394657 / 62500000) ≤ -Real.log (512 / 721) ∧
    -Real.log (512 / 721) ≤ (342314513 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1233)) (n := 12)
    (lo := (21394657 / 62500000)) (hi := (342314513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721 / 512) = 1/(512 / 721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (21394657 / 62500000) (342314513 / 1000000000) (Real.log (721 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (721 / 512) = -Real.log (512 / 721) := by
    rw [show ((721 / 512) : ℝ) = ((512 / 721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (524591819 / 1000000000) ≤ -Real.log (303 / 512) ∧
    -Real.log (303 / 512) ≤ (26229591 / 50000000) := by
  have h := checkLog_sound (w := (209 / 815)) (n := 12)
    (lo := (524591819 / 1000000000)) (hi := (26229591 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 303) = 1/(303 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26229591 / 50000000) (-524591819 / 1000000000) (Real.log (303 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10684323 / 31250000) ≤ -Real.log (5120 / 7207) ∧
    -Real.log (5120 / 7207) ≤ (341898337 / 1000000000) := by
  have h := checkLog_sound (w := (2087 / 12327)) (n := 12)
    (lo := (10684323 / 31250000)) (hi := (341898337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7207 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7207 / 5120) = 1/(5120 / 7207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10684323 / 31250000) (341898337 / 1000000000) (Real.log (7207 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7207 / 5120) = -Real.log (5120 / 7207) := by
    rw [show ((7207 / 5120) : ℝ) = ((5120 / 7207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (52360221 / 100000000) ≤ -Real.log (3033 / 5120) ∧
    -Real.log (3033 / 5120) ≤ (523602211 / 1000000000) := by
  have h := checkLog_sound (w := (2087 / 8153)) (n := 12)
    (lo := (52360221 / 100000000)) (hi := (523602211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3033) = 1/(3033 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-523602211 / 1000000000) (-52360221 / 100000000) (Real.log (3033 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (254932873 / 1000000000) ≤ -Real.log (8000 / 10323) ∧
    -Real.log (8000 / 10323) ≤ (127466437 / 500000000) := by
  have h := checkLog_sound (w := (2323 / 18323)) (n := 12)
    (lo := (254932873 / 1000000000)) (hi := (127466437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10323 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10323 / 8000) = 1/(8000 / 10323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (254932873 / 1000000000) (127466437 / 500000000) (Real.log (10323 / 8000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (10323 / 8000) = -Real.log (8000 / 10323) := by
    rw [show ((10323 / 8000) : ℝ) = ((8000 / 10323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (343018617 / 1000000000) ≤ -Real.log (5677 / 8000) ∧
    -Real.log (5677 / 8000) ≤ (171509309 / 500000000) := by
  have h := checkLog_sound (w := (2323 / 13677)) (n := 12)
    (lo := (343018617 / 1000000000)) (hi := (171509309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 5677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 5677) = 1/(5677 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-171509309 / 500000000) (-343018617 / 1000000000) (Real.log (5677 / 8000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (255262181 / 1000000000) ≤ -Real.log (2500 / 3227) ∧
    -Real.log (2500 / 3227) ≤ (127631091 / 500000000) := by
  have h := checkLog_sound (w := (727 / 5727)) (n := 12)
    (lo := (255262181 / 1000000000)) (hi := (127631091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3227 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3227 / 2500) = 1/(2500 / 3227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (255262181 / 1000000000) (127631091 / 500000000) (Real.log (3227 / 2500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (3227 / 2500) = -Real.log (2500 / 3227) := by
    rw [show ((3227 / 2500) : ℝ) = ((2500 / 3227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (42952213 / 125000000) ≤ -Real.log (1773 / 2500) ∧
    -Real.log (1773 / 2500) ≤ (68723541 / 200000000) := by
  have h := checkLog_sound (w := (727 / 4273)) (n := 12)
    (lo := (42952213 / 125000000)) (hi := (68723541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 1773) = 1/(1773 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-68723541 / 200000000) (-42952213 / 125000000) (Real.log (1773 / 2500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (190813729 / 1000000000) ≤ -Real.log (500000 / 605117) ∧
    -Real.log (500000 / 605117) ≤ (19081373 / 100000000) := by
  have h := checkLog_sound (w := (105117 / 1105117)) (n := 12)
    (lo := (190813729 / 1000000000)) (hi := (19081373 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605117 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605117 / 500000) = 1/(500000 / 605117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (190813729 / 1000000000) (19081373 / 100000000) (Real.log (605117 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (605117 / 500000) = -Real.log (500000 / 605117) := by
    rw [show ((605117 / 500000) : ℝ) = ((500000 / 605117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (236018579 / 1000000000) ≤ -Real.log (394883 / 500000) ∧
    -Real.log (394883 / 500000) ≤ (11800929 / 50000000) := by
  have h := checkLog_sound (w := (105117 / 894883)) (n := 12)
    (lo := (236018579 / 1000000000)) (hi := (11800929 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 394883) = 1/(394883 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-11800929 / 50000000) (-236018579 / 1000000000) (Real.log (394883 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (23885073 / 125000000) ≤ -Real.log (1000000 / 1210557) ∧
    -Real.log (1000000 / 1210557) ≤ (38216117 / 200000000) := by
  have h := checkLog_sound (w := (210557 / 2210557)) (n := 12)
    (lo := (23885073 / 125000000)) (hi := (38216117 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210557 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1210557 / 1000000) = 1/(1000000 / 1210557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (23885073 / 125000000) (38216117 / 200000000) (Real.log (1210557 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1210557 / 1000000) = -Real.log (1000000 / 1210557) := by
    rw [show ((1210557 / 1000000) : ℝ) = ((1000000 / 1210557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (47285529 / 200000000) ≤ -Real.log (789443 / 1000000) ∧
    -Real.log (789443 / 1000000) ≤ (118213823 / 500000000) := by
  have h := checkLog_sound (w := (210557 / 1789443)) (n := 12)
    (lo := (47285529 / 200000000)) (hi := (118213823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 789443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 789443) = 1/(789443 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-118213823 / 500000000) (-47285529 / 200000000) (Real.log (789443 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (597951491 / 1000000000) ≤ -Real.log (500000000000 / 909194997357) ∧
    -Real.log (500000000000 / 909194997357) ≤ (149487873 / 250000000) := by
  have h := checkLog_sound (w := (409194997357 / 1409194997357)) (n := 12)
    (lo := (597951491 / 1000000000)) (hi := (149487873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((909194997357 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(909194997357 / 500000000000) = 1/(500000000000 / 909194997357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (597951491 / 1000000000) (149487873 / 250000000) (Real.log (909194997357 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (909194997357 / 500000000000) = -Real.log (500000000000 / 909194997357) := by
    rw [show ((909194997357 / 500000000000) : ℝ) = ((500000000000 / 909194997357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (119775977 / 200000000) ≤ -Real.log (250000000000 / 455019740553) ∧
    -Real.log (250000000000 / 455019740553) ≤ (299439943 / 500000000) := by
  have h := checkLog_sound (w := (205019740553 / 705019740553)) (n := 12)
    (lo := (119775977 / 200000000)) (hi := (299439943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((455019740553 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(455019740553 / 250000000000) = 1/(250000000000 / 455019740553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (119775977 / 200000000) (299439943 / 500000000) (Real.log (455019740553 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (455019740553 / 250000000000) = -Real.log (250000000000 / 455019740553) := by
    rw [show ((455019740553 / 250000000000) : ℝ) = ((250000000000 / 455019740553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (426832309 / 1000000000) ≤ -Real.log (250000000000 / 383098917907) ∧
    -Real.log (250000000000 / 383098917907) ≤ (42683231 / 100000000) := by
  have h := checkLog_sound (w := (133098917907 / 633098917907)) (n := 12)
    (lo := (426832309 / 1000000000)) (hi := (42683231 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383098917907 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383098917907 / 250000000000) = 1/(250000000000 / 383098917907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (426832309 / 1000000000) (42683231 / 100000000) (Real.log (383098917907 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (383098917907 / 250000000000) = -Real.log (250000000000 / 383098917907) := by
    rw [show ((383098917907 / 250000000000) : ℝ) = ((250000000000 / 383098917907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (427508229 / 1000000000) ≤ -Real.log (125000000000 / 191678974923) ∧
    -Real.log (125000000000 / 191678974923) ≤ (42750823 / 100000000) := by
  have h := checkLog_sound (w := (66678974923 / 316678974923)) (n := 12)
    (lo := (427508229 / 1000000000)) (hi := (42750823 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191678974923 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191678974923 / 125000000000) = 1/(125000000000 / 191678974923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (427508229 / 1000000000) (42750823 / 100000000) (Real.log (191678974923 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (191678974923 / 125000000000) = -Real.log (125000000000 / 191678974923) := by
    rw [show ((191678974923 / 125000000000) : ℝ) = ((125000000000 / 191678974923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0460
