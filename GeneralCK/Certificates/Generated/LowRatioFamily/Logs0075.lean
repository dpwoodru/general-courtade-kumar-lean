import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4800_neg : (42351291 / 250000000) ≤ -Real.log (5000 / 5923) ∧
    -Real.log (5000 / 5923) ≤ (33881033 / 200000000) := by
  have h := checkLog_sound (w := (923 / 10923)) (n := 12)
    (lo := (42351291 / 250000000)) (hi := (33881033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5923 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5923 / 5000) = 1/(5000 / 5923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4800 : Bounds (42351291 / 250000000) (33881033 / 200000000) (Real.log (5923 / 5000)) := by
  have h := reflection_log_4800_neg
  have he : Real.log (5923 / 5000) = -Real.log (5000 / 5923) := by
    rw [show ((5923 / 5000) : ℝ) = ((5000 / 5923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4801_neg : (25509561 / 125000000) ≤ -Real.log (4077 / 5000) ∧
    -Real.log (4077 / 5000) ≤ (204076489 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 9077)) (n := 12)
    (lo := (25509561 / 125000000)) (hi := (204076489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4077) = 1/(4077 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4801 : Bounds (-204076489 / 1000000000) (-25509561 / 125000000) (Real.log (4077 / 5000)) := by
  have h := reflection_log_4801_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4802_neg : (92291 / 500000000) ≤ -Real.log (5000000 / 5000923) ∧
    -Real.log (5000000 / 5000923) ≤ (184583 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 10000923)) (n := 12)
    (lo := (92291 / 500000000)) (hi := (184583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000923 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000923 / 5000000) = 1/(5000000 / 5000923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4802 : Bounds (92291 / 500000000) (184583 / 1000000000) (Real.log (5000923 / 5000000)) := by
  have h := reflection_log_4802_neg
  have he : Real.log (5000923 / 5000000) = -Real.log (5000000 / 5000923) := by
    rw [show ((5000923 / 5000000) : ℝ) = ((5000000 / 5000923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4803_neg : (184617 / 1000000000) ≤ -Real.log (4999077 / 5000000) ∧
    -Real.log (4999077 / 5000000) ≤ (92309 / 500000000) := by
  have h := checkLog_sound (w := (923 / 9999077)) (n := 12)
    (lo := (184617 / 1000000000)) (hi := (92309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999077) = 1/(4999077 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4803 : Bounds (-92309 / 500000000) (-184617 / 1000000000) (Real.log (4999077 / 5000000)) := by
  have h := reflection_log_4803_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4804_neg : (5542447 / 62500000) ≤ -Real.log (100000 / 109273) ∧
    -Real.log (100000 / 109273) ≤ (88679153 / 1000000000) := by
  have h := checkLog_sound (w := (9273 / 209273)) (n := 12)
    (lo := (5542447 / 62500000)) (hi := (88679153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109273 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109273 / 100000) = 1/(100000 / 109273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4804 : Bounds (5542447 / 62500000) (88679153 / 1000000000) (Real.log (109273 / 100000)) := by
  have h := reflection_log_4804_neg
  have he : Real.log (109273 / 100000) = -Real.log (100000 / 109273) := by
    rw [show ((109273 / 100000) : ℝ) = ((100000 / 109273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4805_neg : (24328797 / 250000000) ≤ -Real.log (90727 / 100000) ∧
    -Real.log (90727 / 100000) ≤ (97315189 / 1000000000) := by
  have h := checkLog_sound (w := (9273 / 190727)) (n := 12)
    (lo := (24328797 / 250000000)) (hi := (97315189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90727) = 1/(90727 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4805 : Bounds (-97315189 / 1000000000) (-24328797 / 250000000) (Real.log (90727 / 100000)) := by
  have h := reflection_log_4805_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4806_neg : (44447093 / 500000000) ≤ -Real.log (200000 / 218593) ∧
    -Real.log (200000 / 218593) ≤ (88894187 / 1000000000) := by
  have h := checkLog_sound (w := (18593 / 418593)) (n := 12)
    (lo := (44447093 / 500000000)) (hi := (88894187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218593 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218593 / 200000) = 1/(200000 / 218593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4806 : Bounds (44447093 / 500000000) (88894187 / 1000000000) (Real.log (218593 / 200000)) := by
  have h := reflection_log_4806_neg
  have he : Real.log (218593 / 200000) = -Real.log (200000 / 218593) := by
    rw [show ((218593 / 200000) : ℝ) = ((200000 / 218593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4807_neg : (609839 / 6250000) ≤ -Real.log (181407 / 200000) ∧
    -Real.log (181407 / 200000) ≤ (97574241 / 1000000000) := by
  have h := checkLog_sound (w := (18593 / 381407)) (n := 12)
    (lo := (609839 / 6250000)) (hi := (97574241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181407) = 1/(181407 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4807 : Bounds (-97574241 / 1000000000) (-609839 / 6250000) (Real.log (181407 / 200000)) := by
  have h := reflection_log_4807_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4808_neg : (4340027 / 500000000) ≤ -Real.log (39654300351 / 40000000000) ∧
    -Real.log (39654300351 / 40000000000) ≤ (1736011 / 200000000) := by
  have h := checkLog_sound (w := (345699649 / 79654300351)) (n := 12)
    (lo := (4340027 / 500000000)) (hi := (1736011 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39654300351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39654300351) = 1/(39654300351 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4808 : Bounds (-1736011 / 200000000) (-4340027 / 500000000) (Real.log (39654300351 / 40000000000)) := by
  have h := reflection_log_4808_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4809_neg : (2159009 / 250000000) ≤ -Real.log (9914011471 / 10000000000) ∧
    -Real.log (9914011471 / 10000000000) ≤ (8636037 / 1000000000) := by
  have h := checkLog_sound (w := (85988529 / 19914011471)) (n := 12)
    (lo := (2159009 / 250000000)) (hi := (8636037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9914011471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9914011471) = 1/(9914011471 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4809 : Bounds (-8636037 / 1000000000) (-2159009 / 250000000) (Real.log (9914011471 / 10000000000)) := by
  have h := reflection_log_4809_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4810_neg : (9299717 / 50000000) ≤ -Real.log (500000000000 / 602207722067) ∧
    -Real.log (500000000000 / 602207722067) ≤ (185994341 / 1000000000) := by
  have h := checkLog_sound (w := (102207722067 / 1102207722067)) (n := 12)
    (lo := (9299717 / 50000000)) (hi := (185994341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602207722067 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602207722067 / 500000000000) = 1/(500000000000 / 602207722067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4810 : Bounds (9299717 / 50000000) (185994341 / 1000000000) (Real.log (602207722067 / 500000000000)) := by
  have h := reflection_log_4810_neg
  have he : Real.log (602207722067 / 500000000000) = -Real.log (500000000000 / 602207722067) := by
    rw [show ((602207722067 / 500000000000) : ℝ) = ((500000000000 / 602207722067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4811_neg : (186468427 / 1000000000) ≤ -Real.log (500000000000 / 602493288573) ∧
    -Real.log (500000000000 / 602493288573) ≤ (46617107 / 250000000) := by
  have h := checkLog_sound (w := (102493288573 / 1102493288573)) (n := 12)
    (lo := (186468427 / 1000000000)) (hi := (46617107 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602493288573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602493288573 / 500000000000) = 1/(500000000000 / 602493288573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4811 : Bounds (186468427 / 1000000000) (46617107 / 250000000) (Real.log (602493288573 / 500000000000)) := by
  have h := reflection_log_4811_neg
  have he : Real.log (602493288573 / 500000000000) = -Real.log (500000000000 / 602493288573) := by
    rw [show ((602493288573 / 500000000000) : ℝ) = ((500000000000 / 602493288573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4812_neg : (373274601 / 1000000000) ≤ -Real.log (500000000000 / 726241569589) ∧
    -Real.log (500000000000 / 726241569589) ≤ (186637301 / 500000000) := by
  have h := checkLog_sound (w := (226241569589 / 1226241569589)) (n := 12)
    (lo := (373274601 / 1000000000)) (hi := (186637301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726241569589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726241569589 / 500000000000) = 1/(500000000000 / 726241569589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4812 : Bounds (373274601 / 1000000000) (186637301 / 500000000) (Real.log (726241569589 / 500000000000)) := by
  have h := reflection_log_4812_neg
  have he : Real.log (726241569589 / 500000000000) = -Real.log (500000000000 / 726241569589) := by
    rw [show ((726241569589 / 500000000000) : ℝ) = ((500000000000 / 726241569589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4813_neg : (373481653 / 1000000000) ≤ -Real.log (500000000000 / 726391954869) ∧
    -Real.log (500000000000 / 726391954869) ≤ (186740827 / 500000000) := by
  have h := checkLog_sound (w := (226391954869 / 1226391954869)) (n := 12)
    (lo := (373481653 / 1000000000)) (hi := (186740827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726391954869 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726391954869 / 500000000000) = 1/(500000000000 / 726391954869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4813 : Bounds (373481653 / 1000000000) (186740827 / 500000000) (Real.log (726391954869 / 500000000000)) := by
  have h := reflection_log_4813_neg
  have he : Real.log (726391954869 / 500000000000) = -Real.log (500000000000 / 726391954869) := by
    rw [show ((726391954869 / 500000000000) : ℝ) = ((500000000000 / 726391954869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4814_neg : (169489577 / 1000000000) ≤ -Real.log (10000 / 11847) ∧
    -Real.log (10000 / 11847) ≤ (84744789 / 500000000) := by
  have h := checkLog_sound (w := (1847 / 21847)) (n := 12)
    (lo := (169489577 / 1000000000)) (hi := (84744789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11847 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11847 / 10000) = 1/(10000 / 11847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4814 : Bounds (169489577 / 1000000000) (84744789 / 500000000) (Real.log (11847 / 10000)) := by
  have h := reflection_log_4814_neg
  have he : Real.log (11847 / 10000) = -Real.log (10000 / 11847) := by
    rw [show ((11847 / 10000) : ℝ) = ((10000 / 11847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4815_neg : (40839827 / 200000000) ≤ -Real.log (8153 / 10000) ∧
    -Real.log (8153 / 10000) ≤ (6381223 / 31250000) := by
  have h := checkLog_sound (w := (1847 / 18153)) (n := 12)
    (lo := (40839827 / 200000000)) (hi := (6381223 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8153) = 1/(8153 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4815 : Bounds (-6381223 / 31250000) (-40839827 / 200000000) (Real.log (8153 / 10000)) := by
  have h := reflection_log_4815_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4816_neg : (92341 / 500000000) ≤ -Real.log (10000000 / 10001847) ∧
    -Real.log (10000000 / 10001847) ≤ (184683 / 1000000000) := by
  have h := checkLog_sound (w := (1847 / 20001847)) (n := 12)
    (lo := (92341 / 500000000)) (hi := (184683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001847 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001847 / 10000000) = 1/(10000000 / 10001847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4816 : Bounds (92341 / 500000000) (184683 / 1000000000) (Real.log (10001847 / 10000000)) := by
  have h := reflection_log_4816_neg
  have he : Real.log (10001847 / 10000000) = -Real.log (10000000 / 10001847) := by
    rw [show ((10001847 / 10000000) : ℝ) = ((10000000 / 10001847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4817_neg : (184717 / 1000000000) ≤ -Real.log (9998153 / 10000000) ∧
    -Real.log (9998153 / 10000000) ≤ (92359 / 500000000) := by
  have h := checkLog_sound (w := (1847 / 19998153)) (n := 12)
    (lo := (184717 / 1000000000)) (hi := (92359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998153) = 1/(9998153 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4817 : Bounds (-92359 / 500000000) (-184717 / 1000000000) (Real.log (9998153 / 10000000)) := by
  have h := reflection_log_4817_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4818_neg : (88725823 / 1000000000) ≤ -Real.log (1000000 / 1092781) ∧
    -Real.log (1000000 / 1092781) ≤ (1386341 / 15625000) := by
  have h := checkLog_sound (w := (92781 / 2092781)) (n := 12)
    (lo := (88725823 / 1000000000)) (hi := (1386341 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092781 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092781 / 1000000) = 1/(1000000 / 1092781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4818 : Bounds (88725823 / 1000000000) (1386341 / 15625000) (Real.log (1092781 / 1000000)) := by
  have h := reflection_log_4818_neg
  have he : Real.log (1092781 / 1000000) = -Real.log (1000000 / 1092781) := by
    rw [show ((1092781 / 1000000) : ℝ) = ((1000000 / 1092781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4819_neg : (48685701 / 500000000) ≤ -Real.log (907219 / 1000000) ∧
    -Real.log (907219 / 1000000) ≤ (97371403 / 1000000000) := by
  have h := checkLog_sound (w := (92781 / 1907219)) (n := 12)
    (lo := (48685701 / 500000000)) (hi := (97371403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907219) = 1/(907219 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4819 : Bounds (-97371403 / 1000000000) (-48685701 / 500000000) (Real.log (907219 / 1000000)) := by
  have h := reflection_log_4819_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4820_neg : (88940847 / 1000000000) ≤ -Real.log (125000 / 136627) ∧
    -Real.log (125000 / 136627) ≤ (5558803 / 62500000) := by
  have h := checkLog_sound (w := (11627 / 261627)) (n := 12)
    (lo := (88940847 / 1000000000)) (hi := (5558803 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136627 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136627 / 125000) = 1/(125000 / 136627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4820 : Bounds (88940847 / 1000000000) (5558803 / 62500000) (Real.log (136627 / 125000)) := by
  have h := reflection_log_4820_neg
  have he : Real.log (136627 / 125000) = -Real.log (125000 / 136627) := by
    rw [show ((136627 / 125000) : ℝ) = ((125000 / 136627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4821_neg : (97630469 / 1000000000) ≤ -Real.log (113373 / 125000) ∧
    -Real.log (113373 / 125000) ≤ (9763047 / 100000000) := by
  have h := checkLog_sound (w := (11627 / 238373)) (n := 12)
    (lo := (97630469 / 1000000000)) (hi := (9763047 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113373) = 1/(113373 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4821 : Bounds (-9763047 / 100000000) (-97630469 / 1000000000) (Real.log (113373 / 125000)) := by
  have h := reflection_log_4821_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4822_neg : (8689621 / 1000000000) ≤ -Real.log (15489812871 / 15625000000) ∧
    -Real.log (15489812871 / 15625000000) ≤ (4344811 / 500000000) := by
  have h := checkLog_sound (w := (135187129 / 31114812871)) (n := 12)
    (lo := (8689621 / 1000000000)) (hi := (4344811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15489812871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15489812871) = 1/(15489812871 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4822 : Bounds (-4344811 / 500000000) (-8689621 / 1000000000) (Real.log (15489812871 / 15625000000)) := by
  have h := reflection_log_4822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4823_neg : (8645579 / 1000000000) ≤ -Real.log (991391686039 / 1000000000000) ∧
    -Real.log (991391686039 / 1000000000000) ≤ (432279 / 50000000) := by
  have h := checkLog_sound (w := (8608313961 / 1991391686039)) (n := 12)
    (lo := (8645579 / 1000000000)) (hi := (432279 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991391686039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991391686039) = 1/(991391686039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4823 : Bounds (-432279 / 50000000) (-8645579 / 1000000000) (Real.log (991391686039 / 1000000000000)) := by
  have h := reflection_log_4823_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4824_neg : (7443889 / 40000000) ≤ -Real.log (100000000000 / 120453936701) ∧
    -Real.log (100000000000 / 120453936701) ≤ (93048613 / 500000000) := by
  have h := checkLog_sound (w := (20453936701 / 220453936701)) (n := 12)
    (lo := (7443889 / 40000000)) (hi := (93048613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120453936701 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120453936701 / 100000000000) = 1/(100000000000 / 120453936701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4824 : Bounds (7443889 / 40000000) (93048613 / 500000000) (Real.log (120453936701 / 100000000000)) := by
  have h := reflection_log_4824_neg
  have he : Real.log (120453936701 / 100000000000) = -Real.log (100000000000 / 120453936701) := by
    rw [show ((120453936701 / 100000000000) : ℝ) = ((100000000000 / 120453936701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4825_neg : (186571317 / 1000000000) ≤ -Real.log (250000000000 / 301277641061) ∧
    -Real.log (250000000000 / 301277641061) ≤ (93285659 / 500000000) := by
  have h := checkLog_sound (w := (51277641061 / 551277641061)) (n := 12)
    (lo := (186571317 / 1000000000)) (hi := (93285659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301277641061 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301277641061 / 250000000000) = 1/(250000000000 / 301277641061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4825 : Bounds (186571317 / 1000000000) (93285659 / 500000000) (Real.log (301277641061 / 250000000000)) := by
  have h := reflection_log_4825_neg
  have he : Real.log (301277641061 / 250000000000) = -Real.log (250000000000 / 301277641061) := by
    rw [show ((301277641061 / 250000000000) : ℝ) = ((250000000000 / 301277641061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4826_neg : (373481653 / 1000000000) ≤ -Real.log (125000000000 / 181597988717) ∧
    -Real.log (125000000000 / 181597988717) ≤ (186740827 / 500000000) := by
  have h := checkLog_sound (w := (56597988717 / 306597988717)) (n := 12)
    (lo := (373481653 / 1000000000)) (hi := (186740827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181597988717 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181597988717 / 125000000000) = 1/(125000000000 / 181597988717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4826 : Bounds (373481653 / 1000000000) (186740827 / 500000000) (Real.log (181597988717 / 125000000000)) := by
  have h := reflection_log_4826_neg
  have he : Real.log (181597988717 / 125000000000) = -Real.log (125000000000 / 181597988717) := by
    rw [show ((181597988717 / 125000000000) : ℝ) = ((125000000000 / 181597988717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4827_neg : (373688713 / 1000000000) ≤ -Real.log (6250000000 / 9081779713) ∧
    -Real.log (6250000000 / 9081779713) ≤ (186844357 / 500000000) := by
  have h := checkLog_sound (w := (2831779713 / 15331779713)) (n := 12)
    (lo := (373688713 / 1000000000)) (hi := (186844357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9081779713 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9081779713 / 6250000000) = 1/(6250000000 / 9081779713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4827 : Bounds (373688713 / 1000000000) (186844357 / 500000000) (Real.log (9081779713 / 6250000000)) := by
  have h := reflection_log_4827_neg
  have he : Real.log (9081779713 / 6250000000) = -Real.log (6250000000 / 9081779713) := by
    rw [show ((9081779713 / 6250000000) : ℝ) = ((6250000000 / 9081779713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4828_neg : (169573983 / 1000000000) ≤ -Real.log (1250 / 1481) ∧
    -Real.log (1250 / 1481) ≤ (5299187 / 31250000) := by
  have h := checkLog_sound (w := (231 / 2731)) (n := 12)
    (lo := (169573983 / 1000000000)) (hi := (5299187 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1481 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1481 / 1250) = 1/(1250 / 1481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4828 : Bounds (169573983 / 1000000000) (5299187 / 31250000) (Real.log (1481 / 1250)) := by
  have h := reflection_log_4828_neg
  have he : Real.log (1481 / 1250) = -Real.log (1250 / 1481) := by
    rw [show ((1481 / 1250) : ℝ) = ((1250 / 1481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4829_neg : (204321797 / 1000000000) ≤ -Real.log (1019 / 1250) ∧
    -Real.log (1019 / 1250) ≤ (102160899 / 500000000) := by
  have h := checkLog_sound (w := (231 / 2269)) (n := 12)
    (lo := (204321797 / 1000000000)) (hi := (102160899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1019) = 1/(1019 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4829 : Bounds (-102160899 / 500000000) (-204321797 / 1000000000) (Real.log (1019 / 1250)) := by
  have h := reflection_log_4829_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4830_neg : (92391 / 500000000) ≤ -Real.log (1250000 / 1250231) ∧
    -Real.log (1250000 / 1250231) ≤ (184783 / 1000000000) := by
  have h := checkLog_sound (w := (231 / 2500231)) (n := 12)
    (lo := (92391 / 500000000)) (hi := (184783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250231 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250231 / 1250000) = 1/(1250000 / 1250231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4830 : Bounds (92391 / 500000000) (184783 / 1000000000) (Real.log (1250231 / 1250000)) := by
  have h := reflection_log_4830_neg
  have he : Real.log (1250231 / 1250000) = -Real.log (1250000 / 1250231) := by
    rw [show ((1250231 / 1250000) : ℝ) = ((1250000 / 1250231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4831_neg : (184817 / 1000000000) ≤ -Real.log (1249769 / 1250000) ∧
    -Real.log (1249769 / 1250000) ≤ (92409 / 500000000) := by
  have h := checkLog_sound (w := (231 / 2499769)) (n := 12)
    (lo := (184817 / 1000000000)) (hi := (92409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249769) = 1/(1249769 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4831 : Bounds (-92409 / 500000000) (-184817 / 1000000000) (Real.log (1249769 / 1250000)) := by
  have h := reflection_log_4831_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4832_neg : (88772491 / 1000000000) ≤ -Real.log (31250 / 34151) ∧
    -Real.log (31250 / 34151) ≤ (22193123 / 250000000) := by
  have h := checkLog_sound (w := (2901 / 65401)) (n := 12)
    (lo := (88772491 / 1000000000)) (hi := (22193123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34151 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34151 / 31250) = 1/(31250 / 34151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4832 : Bounds (88772491 / 1000000000) (22193123 / 250000000) (Real.log (34151 / 31250)) := by
  have h := reflection_log_4832_neg
  have he : Real.log (34151 / 31250) = -Real.log (31250 / 34151) := by
    rw [show ((34151 / 31250) : ℝ) = ((31250 / 34151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4833_neg : (97427619 / 1000000000) ≤ -Real.log (28349 / 31250) ∧
    -Real.log (28349 / 31250) ≤ (4871381 / 50000000) := by
  have h := checkLog_sound (w := (2901 / 59599)) (n := 12)
    (lo := (97427619 / 1000000000)) (hi := (4871381 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28349) = 1/(28349 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4833 : Bounds (-4871381 / 50000000) (-97427619 / 1000000000) (Real.log (28349 / 31250)) := by
  have h := reflection_log_4833_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4834_neg : (44493753 / 500000000) ≤ -Real.log (1000000 / 1093067) ∧
    -Real.log (1000000 / 1093067) ≤ (88987507 / 1000000000) := by
  have h := checkLog_sound (w := (93067 / 2093067)) (n := 12)
    (lo := (44493753 / 500000000)) (hi := (88987507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093067 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093067 / 1000000) = 1/(1000000 / 1093067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4834 : Bounds (44493753 / 500000000) (88987507 / 1000000000) (Real.log (1093067 / 1000000)) := by
  have h := reflection_log_4834_neg
  have he : Real.log (1093067 / 1000000) = -Real.log (1000000 / 1093067) := by
    rw [show ((1093067 / 1000000) : ℝ) = ((1000000 / 1093067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4835_neg : (97686701 / 1000000000) ≤ -Real.log (906933 / 1000000) ∧
    -Real.log (906933 / 1000000) ≤ (48843351 / 500000000) := by
  have h := checkLog_sound (w := (93067 / 1906933)) (n := 12)
    (lo := (97686701 / 1000000000)) (hi := (48843351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906933) = 1/(906933 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4835 : Bounds (-48843351 / 500000000) (-97686701 / 1000000000) (Real.log (906933 / 1000000)) := by
  have h := reflection_log_4835_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4836_neg : (1739839 / 200000000) ≤ -Real.log (991338533511 / 1000000000000) ∧
    -Real.log (991338533511 / 1000000000000) ≤ (2174799 / 250000000) := by
  have h := checkLog_sound (w := (8661466489 / 1991338533511)) (n := 12)
    (lo := (1739839 / 200000000)) (hi := (2174799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991338533511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991338533511) = 1/(991338533511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4836 : Bounds (-2174799 / 250000000) (-1739839 / 200000000) (Real.log (991338533511 / 1000000000000)) := by
  have h := reflection_log_4836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4837_neg : (1081891 / 125000000) ≤ -Real.log (968146699 / 976562500) ∧
    -Real.log (968146699 / 976562500) ≤ (8655129 / 1000000000) := by
  have h := checkLog_sound (w := (8415801 / 1944709199)) (n := 12)
    (lo := (1081891 / 125000000)) (hi := (8655129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 968146699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 968146699) = 1/(968146699 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4837 : Bounds (-8655129 / 1000000000) (-1081891 / 125000000) (Real.log (968146699 / 976562500)) := by
  have h := reflection_log_4837_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4838_neg : (186200111 / 1000000000) ≤ -Real.log (50000000000 / 60233165191) ∧
    -Real.log (50000000000 / 60233165191) ≤ (11637507 / 62500000) := by
  have h := checkLog_sound (w := (10233165191 / 110233165191)) (n := 12)
    (lo := (186200111 / 1000000000)) (hi := (11637507 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60233165191 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60233165191 / 50000000000) = 1/(50000000000 / 60233165191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4838 : Bounds (186200111 / 1000000000) (11637507 / 62500000) (Real.log (60233165191 / 50000000000)) := by
  have h := reflection_log_4838_neg
  have he : Real.log (60233165191 / 50000000000) = -Real.log (50000000000 / 60233165191) := by
    rw [show ((60233165191 / 50000000000) : ℝ) = ((50000000000 / 60233165191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4839_neg : (186674207 / 1000000000) ≤ -Real.log (125000000000 / 150654320661) ∧
    -Real.log (125000000000 / 150654320661) ≤ (5833569 / 31250000) := by
  have h := checkLog_sound (w := (25654320661 / 275654320661)) (n := 12)
    (lo := (186674207 / 1000000000)) (hi := (5833569 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150654320661 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150654320661 / 125000000000) = 1/(125000000000 / 150654320661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4839 : Bounds (186674207 / 1000000000) (5833569 / 31250000) (Real.log (150654320661 / 125000000000)) := by
  have h := reflection_log_4839_neg
  have he : Real.log (150654320661 / 125000000000) = -Real.log (125000000000 / 150654320661) := by
    rw [show ((150654320661 / 125000000000) : ℝ) = ((125000000000 / 150654320661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4840_neg : (373688713 / 1000000000) ≤ -Real.log (500000000000 / 726542377039) ∧
    -Real.log (500000000000 / 726542377039) ≤ (186844357 / 500000000) := by
  have h := checkLog_sound (w := (226542377039 / 1226542377039)) (n := 12)
    (lo := (373688713 / 1000000000)) (hi := (186844357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726542377039 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726542377039 / 500000000000) = 1/(500000000000 / 726542377039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4840 : Bounds (373688713 / 1000000000) (186844357 / 500000000) (Real.log (726542377039 / 500000000000)) := by
  have h := reflection_log_4840_neg
  have he : Real.log (726542377039 / 500000000000) = -Real.log (500000000000 / 726542377039) := by
    rw [show ((726542377039 / 500000000000) : ℝ) = ((500000000000 / 726542377039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4841_neg : (373895781 / 1000000000) ≤ -Real.log (250000000000 / 363346418057) ∧
    -Real.log (250000000000 / 363346418057) ≤ (186947891 / 500000000) := by
  have h := checkLog_sound (w := (113346418057 / 613346418057)) (n := 12)
    (lo := (373895781 / 1000000000)) (hi := (186947891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363346418057 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363346418057 / 250000000000) = 1/(250000000000 / 363346418057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4841 : Bounds (373895781 / 1000000000) (186947891 / 500000000) (Real.log (363346418057 / 250000000000)) := by
  have h := reflection_log_4841_neg
  have he : Real.log (363346418057 / 250000000000) = -Real.log (250000000000 / 363346418057) := by
    rw [show ((363346418057 / 250000000000) : ℝ) = ((250000000000 / 363346418057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4842_neg : (84829191 / 500000000) ≤ -Real.log (10000 / 11849) ∧
    -Real.log (10000 / 11849) ≤ (169658383 / 1000000000) := by
  have h := checkLog_sound (w := (1849 / 21849)) (n := 12)
    (lo := (84829191 / 500000000)) (hi := (169658383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11849 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11849 / 10000) = 1/(10000 / 11849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4842 : Bounds (84829191 / 500000000) (169658383 / 1000000000) (Real.log (11849 / 10000)) := by
  have h := reflection_log_4842_neg
  have he : Real.log (11849 / 10000) = -Real.log (10000 / 11849) := by
    rw [show ((11849 / 10000) : ℝ) = ((10000 / 11849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4843_neg : (204444473 / 1000000000) ≤ -Real.log (8151 / 10000) ∧
    -Real.log (8151 / 10000) ≤ (102222237 / 500000000) := by
  have h := checkLog_sound (w := (1849 / 18151)) (n := 12)
    (lo := (204444473 / 1000000000)) (hi := (102222237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8151) = 1/(8151 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4843 : Bounds (-102222237 / 500000000) (-204444473 / 1000000000) (Real.log (8151 / 10000)) := by
  have h := reflection_log_4843_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4844_neg : (92441 / 500000000) ≤ -Real.log (10000000 / 10001849) ∧
    -Real.log (10000000 / 10001849) ≤ (184883 / 1000000000) := by
  have h := checkLog_sound (w := (1849 / 20001849)) (n := 12)
    (lo := (92441 / 500000000)) (hi := (184883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001849 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001849 / 10000000) = 1/(10000000 / 10001849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4844 : Bounds (92441 / 500000000) (184883 / 1000000000) (Real.log (10001849 / 10000000)) := by
  have h := reflection_log_4844_neg
  have he : Real.log (10001849 / 10000000) = -Real.log (10000000 / 10001849) := by
    rw [show ((10001849 / 10000000) : ℝ) = ((10000000 / 10001849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4845_neg : (184917 / 1000000000) ≤ -Real.log (9998151 / 10000000) ∧
    -Real.log (9998151 / 10000000) ≤ (92459 / 500000000) := by
  have h := checkLog_sound (w := (1849 / 19998151)) (n := 12)
    (lo := (184917 / 1000000000)) (hi := (92459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998151) = 1/(9998151 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4845 : Bounds (-92459 / 500000000) (-184917 / 1000000000) (Real.log (9998151 / 10000000)) := by
  have h := reflection_log_4845_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4846_neg : (88818243 / 1000000000) ≤ -Real.log (500000 / 546441) ∧
    -Real.log (500000 / 546441) ≤ (22204561 / 250000000) := by
  have h := checkLog_sound (w := (46441 / 1046441)) (n := 12)
    (lo := (88818243 / 1000000000)) (hi := (22204561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546441 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546441 / 500000) = 1/(500000 / 546441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4846 : Bounds (88818243 / 1000000000) (22204561 / 250000000) (Real.log (546441 / 500000)) := by
  have h := reflection_log_4846_neg
  have he : Real.log (546441 / 500000) = -Real.log (500000 / 546441) := by
    rw [show ((546441 / 500000) : ℝ) = ((500000 / 546441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4847_neg : (48741369 / 500000000) ≤ -Real.log (453559 / 500000) ∧
    -Real.log (453559 / 500000) ≤ (97482739 / 1000000000) := by
  have h := checkLog_sound (w := (46441 / 953559)) (n := 12)
    (lo := (48741369 / 500000000)) (hi := (97482739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453559) = 1/(453559 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4847 : Bounds (-97482739 / 1000000000) (-48741369 / 500000000) (Real.log (453559 / 500000)) := by
  have h := reflection_log_4847_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4848_neg : (89034163 / 1000000000) ≤ -Real.log (500000 / 546559) ∧
    -Real.log (500000 / 546559) ≤ (22258541 / 250000000) := by
  have h := checkLog_sound (w := (46559 / 1046559)) (n := 12)
    (lo := (89034163 / 1000000000)) (hi := (22258541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546559 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546559 / 500000) = 1/(500000 / 546559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4848 : Bounds (89034163 / 1000000000) (22258541 / 250000000) (Real.log (546559 / 500000)) := by
  have h := reflection_log_4848_neg
  have he : Real.log (546559 / 500000) = -Real.log (500000 / 546559) := by
    rw [show ((546559 / 500000) : ℝ) = ((500000 / 546559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4849_neg : (12217867 / 125000000) ≤ -Real.log (453441 / 500000) ∧
    -Real.log (453441 / 500000) ≤ (97742937 / 1000000000) := by
  have h := checkLog_sound (w := (46559 / 953441)) (n := 12)
    (lo := (12217867 / 125000000)) (hi := (97742937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453441) = 1/(453441 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4849 : Bounds (-97742937 / 1000000000) (-12217867 / 125000000) (Real.log (453441 / 500000)) := by
  have h := reflection_log_4849_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4850_neg : (8708773 / 1000000000) ≤ -Real.log (247832259519 / 250000000000) ∧
    -Real.log (247832259519 / 250000000000) ≤ (4354387 / 500000000) := by
  have h := checkLog_sound (w := (2167740481 / 497832259519)) (n := 12)
    (lo := (8708773 / 1000000000)) (hi := (4354387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247832259519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247832259519) = 1/(247832259519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4850 : Bounds (-4354387 / 500000000) (-8708773 / 1000000000) (Real.log (247832259519 / 250000000000)) := by
  have h := reflection_log_4850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4851_neg : (4332247 / 500000000) ≤ -Real.log (247843233519 / 250000000000) ∧
    -Real.log (247843233519 / 250000000000) ≤ (1732899 / 200000000) := by
  have h := checkLog_sound (w := (2156766481 / 497843233519)) (n := 12)
    (lo := (4332247 / 500000000)) (hi := (1732899 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247843233519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247843233519) = 1/(247843233519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4851 : Bounds (-1732899 / 200000000) (-4332247 / 500000000) (Real.log (247843233519 / 250000000000)) := by
  have h := reflection_log_4851_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4852_neg : (186300981 / 1000000000) ≤ -Real.log (125000000000 / 150598103003) ∧
    -Real.log (125000000000 / 150598103003) ≤ (93150491 / 500000000) := by
  have h := checkLog_sound (w := (25598103003 / 275598103003)) (n := 12)
    (lo := (186300981 / 1000000000)) (hi := (93150491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150598103003 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150598103003 / 125000000000) = 1/(125000000000 / 150598103003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4852 : Bounds (186300981 / 1000000000) (93150491 / 500000000) (Real.log (150598103003 / 125000000000)) := by
  have h := reflection_log_4852_neg
  have he : Real.log (150598103003 / 125000000000) = -Real.log (125000000000 / 150598103003) := by
    rw [show ((150598103003 / 125000000000) : ℝ) = ((125000000000 / 150598103003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4853_neg : (186777099 / 1000000000) ≤ -Real.log (25000000000 / 30133964507) ∧
    -Real.log (25000000000 / 30133964507) ≤ (1867771 / 10000000) := by
  have h := checkLog_sound (w := (5133964507 / 55133964507)) (n := 12)
    (lo := (186777099 / 1000000000)) (hi := (1867771 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30133964507 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30133964507 / 25000000000) = 1/(25000000000 / 30133964507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4853 : Bounds (186777099 / 1000000000) (1867771 / 10000000) (Real.log (30133964507 / 25000000000)) := by
  have h := reflection_log_4853_neg
  have he : Real.log (30133964507 / 25000000000) = -Real.log (25000000000 / 30133964507) := by
    rw [show ((30133964507 / 25000000000) : ℝ) = ((25000000000 / 30133964507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4854_neg : (373895781 / 1000000000) ≤ -Real.log (500000000000 / 726692836113) ∧
    -Real.log (500000000000 / 726692836113) ≤ (186947891 / 500000000) := by
  have h := checkLog_sound (w := (226692836113 / 1226692836113)) (n := 12)
    (lo := (373895781 / 1000000000)) (hi := (186947891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726692836113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726692836113 / 500000000000) = 1/(500000000000 / 726692836113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4854 : Bounds (373895781 / 1000000000) (186947891 / 500000000) (Real.log (726692836113 / 500000000000)) := by
  have h := reflection_log_4854_neg
  have he : Real.log (726692836113 / 500000000000) = -Real.log (500000000000 / 726692836113) := by
    rw [show ((726692836113 / 500000000000) : ℝ) = ((500000000000 / 726692836113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4855_neg : (46762857 / 125000000) ≤ -Real.log (500000000000 / 726843332107) ∧
    -Real.log (500000000000 / 726843332107) ≤ (374102857 / 1000000000) := by
  have h := checkLog_sound (w := (226843332107 / 1226843332107)) (n := 12)
    (lo := (46762857 / 125000000)) (hi := (374102857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726843332107 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726843332107 / 500000000000) = 1/(500000000000 / 726843332107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4855 : Bounds (46762857 / 125000000) (374102857 / 1000000000) (Real.log (726843332107 / 500000000000)) := by
  have h := reflection_log_4855_neg
  have he : Real.log (726843332107 / 500000000000) = -Real.log (500000000000 / 726843332107) := by
    rw [show ((726843332107 / 500000000000) : ℝ) = ((500000000000 / 726843332107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4856_neg : (84871387 / 500000000) ≤ -Real.log (200 / 237) ∧
    -Real.log (200 / 237) ≤ (6789711 / 40000000) := by
  have h := checkLog_sound (w := (37 / 437)) (n := 12)
    (lo := (84871387 / 500000000)) (hi := (6789711 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237 / 200) = 1/(200 / 237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4856 : Bounds (84871387 / 500000000) (6789711 / 40000000) (Real.log (237 / 200)) := by
  have h := reflection_log_4856_neg
  have he : Real.log (237 / 200) = -Real.log (200 / 237) := by
    rw [show ((237 / 200) : ℝ) = ((200 / 237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4857_neg : (40913433 / 200000000) ≤ -Real.log (163 / 200) ∧
    -Real.log (163 / 200) ≤ (102283583 / 500000000) := by
  have h := checkLog_sound (w := (37 / 363)) (n := 12)
    (lo := (40913433 / 200000000)) (hi := (102283583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 163) = 1/(163 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4857 : Bounds (-102283583 / 500000000) (-40913433 / 200000000) (Real.log (163 / 200)) := by
  have h := reflection_log_4857_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4858_neg : (92491 / 500000000) ≤ -Real.log (200000 / 200037) ∧
    -Real.log (200000 / 200037) ≤ (184983 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 400037)) (n := 12)
    (lo := (92491 / 500000000)) (hi := (184983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200037 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200037 / 200000) = 1/(200000 / 200037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4858 : Bounds (92491 / 500000000) (184983 / 1000000000) (Real.log (200037 / 200000)) := by
  have h := reflection_log_4858_neg
  have he : Real.log (200037 / 200000) = -Real.log (200000 / 200037) := by
    rw [show ((200037 / 200000) : ℝ) = ((200000 / 200037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4859_neg : (185017 / 1000000000) ≤ -Real.log (199963 / 200000) ∧
    -Real.log (199963 / 200000) ≤ (92509 / 500000000) := by
  have h := checkLog_sound (w := (37 / 399963)) (n := 12)
    (lo := (185017 / 1000000000)) (hi := (92509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199963) = 1/(199963 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4859 : Bounds (-92509 / 500000000) (-185017 / 1000000000) (Real.log (199963 / 200000)) := by
  have h := reflection_log_4859_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4860_neg : (22216227 / 250000000) ≤ -Real.log (1000000 / 1092933) ∧
    -Real.log (1000000 / 1092933) ≤ (88864909 / 1000000000) := by
  have h := checkLog_sound (w := (92933 / 2092933)) (n := 12)
    (lo := (22216227 / 250000000)) (hi := (88864909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092933 / 1000000) = 1/(1000000 / 1092933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4860 : Bounds (22216227 / 250000000) (88864909 / 1000000000) (Real.log (1092933 / 1000000)) := by
  have h := reflection_log_4860_neg
  have he : Real.log (1092933 / 1000000) = -Real.log (1000000 / 1092933) := by
    rw [show ((1092933 / 1000000) : ℝ) = ((1000000 / 1092933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4861_neg : (97538961 / 1000000000) ≤ -Real.log (907067 / 1000000) ∧
    -Real.log (907067 / 1000000) ≤ (48769481 / 500000000) := by
  have h := checkLog_sound (w := (92933 / 1907067)) (n := 12)
    (lo := (97538961 / 1000000000)) (hi := (48769481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907067) = 1/(907067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4861 : Bounds (-48769481 / 500000000) (-97538961 / 1000000000) (Real.log (907067 / 1000000)) := by
  have h := reflection_log_4861_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4862_neg : (89080817 / 1000000000) ≤ -Real.log (1000000 / 1093169) ∧
    -Real.log (1000000 / 1093169) ≤ (44540409 / 500000000) := by
  have h := checkLog_sound (w := (93169 / 2093169)) (n := 12)
    (lo := (89080817 / 1000000000)) (hi := (44540409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093169 / 1000000) = 1/(1000000 / 1093169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4862 : Bounds (89080817 / 1000000000) (44540409 / 500000000) (Real.log (1093169 / 1000000)) := by
  have h := reflection_log_4862_neg
  have he : Real.log (1093169 / 1000000) = -Real.log (1000000 / 1093169) := by
    rw [show ((1093169 / 1000000) : ℝ) = ((1000000 / 1093169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4863_neg : (48899587 / 500000000) ≤ -Real.log (906831 / 1000000) ∧
    -Real.log (906831 / 1000000) ≤ (3911967 / 40000000) := by
  have h := checkLog_sound (w := (93169 / 1906831)) (n := 12)
    (lo := (48899587 / 500000000)) (hi := (3911967 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906831) = 1/(906831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4863 : Bounds (-3911967 / 40000000) (-48899587 / 500000000) (Real.log (906831 / 1000000)) := by
  have h := reflection_log_4863_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
