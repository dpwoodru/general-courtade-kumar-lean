import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2944_neg : (89892979 / 1000000000) ≤ -Real.log (914029 / 1000000) ∧
    -Real.log (914029 / 1000000) ≤ (4494649 / 50000000) := by
  have h := checkLog_sound (w := (85971 / 1914029)) (n := 12)
    (lo := (89892979 / 1000000000)) (hi := (4494649 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914029) = 1/(914029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2944 : Bounds (-4494649 / 50000000) (-89892979 / 1000000000) (Real.log (914029 / 1000000)) := by
  have h := reflection_log_2944_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2945_neg : (41339461 / 500000000) ≤ -Real.log (1000000 / 1086193) ∧
    -Real.log (1000000 / 1086193) ≤ (82678923 / 1000000000) := by
  have h := checkLog_sound (w := (86193 / 2086193)) (n := 12)
    (lo := (41339461 / 500000000)) (hi := (82678923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1086193 / 1000000) = 1/(1000000 / 1086193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2945 : Bounds (41339461 / 500000000) (82678923 / 1000000000) (Real.log (1086193 / 1000000)) := by
  have h := reflection_log_2945_neg
  have he : Real.log (1086193 / 1000000) = -Real.log (1000000 / 1086193) := by
    rw [show ((1086193 / 1000000) : ℝ) = ((1000000 / 1086193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2946_neg : (90135889 / 1000000000) ≤ -Real.log (913807 / 1000000) ∧
    -Real.log (913807 / 1000000) ≤ (9013589 / 100000000) := by
  have h := checkLog_sound (w := (86193 / 1913807)) (n := 12)
    (lo := (90135889 / 1000000000)) (hi := (9013589 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 913807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 913807) = 1/(913807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2946 : Bounds (-9013589 / 100000000) (-90135889 / 1000000000) (Real.log (913807 / 1000000)) := by
  have h := reflection_log_2946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2947_neg : (7456967 / 1000000000) ≤ -Real.log (992570766751 / 1000000000000) ∧
    -Real.log (992570766751 / 1000000000000) ≤ (932121 / 125000000) := by
  have h := checkLog_sound (w := (7429233249 / 1992570766751)) (n := 12)
    (lo := (7456967 / 1000000000)) (hi := (932121 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992570766751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992570766751) = 1/(992570766751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2947 : Bounds (-932121 / 125000000) (-7456967 / 1000000000) (Real.log (992570766751 / 1000000000000)) := by
  have h := reflection_log_2947_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2948_neg : (7418461 / 1000000000) ≤ -Real.log (992608987159 / 1000000000000) ∧
    -Real.log (992608987159 / 1000000000000) ≤ (3709231 / 500000000) := by
  have h := checkLog_sound (w := (7391012841 / 1992608987159)) (n := 12)
    (lo := (7418461 / 1000000000)) (hi := (3709231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992608987159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992608987159) = 1/(992608987159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2948 : Bounds (-3709231 / 500000000) (-7418461 / 1000000000) (Real.log (992608987159 / 1000000000000)) := by
  have h := reflection_log_2948_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2949_neg : (172367497 / 1000000000) ≤ -Real.log (100000000000 / 118811438149) ∧
    -Real.log (100000000000 / 118811438149) ≤ (86183749 / 500000000) := by
  have h := checkLog_sound (w := (18811438149 / 218811438149)) (n := 12)
    (lo := (172367497 / 1000000000)) (hi := (86183749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118811438149 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118811438149 / 100000000000) = 1/(100000000000 / 118811438149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2949 : Bounds (172367497 / 1000000000) (86183749 / 500000000) (Real.log (118811438149 / 100000000000)) := by
  have h := reflection_log_2949_neg
  have he : Real.log (118811438149 / 100000000000) = -Real.log (100000000000 / 118811438149) := by
    rw [show ((118811438149 / 100000000000) : ℝ) = ((100000000000 / 118811438149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2950_neg : (172814811 / 1000000000) ≤ -Real.log (250000000000 / 297161490337) ∧
    -Real.log (250000000000 / 297161490337) ≤ (43203703 / 250000000) := by
  have h := checkLog_sound (w := (47161490337 / 547161490337)) (n := 12)
    (lo := (172814811 / 1000000000)) (hi := (43203703 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297161490337 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297161490337 / 250000000000) = 1/(250000000000 / 297161490337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2950 : Bounds (172814811 / 1000000000) (43203703 / 250000000) (Real.log (297161490337 / 250000000000)) := by
  have h := reflection_log_2950_neg
  have he : Real.log (297161490337 / 250000000000) = -Real.log (250000000000 / 297161490337) := by
    rw [show ((297161490337 / 250000000000) : ℝ) = ((250000000000 / 297161490337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2951_neg : (345805271 / 1000000000) ≤ -Real.log (500000000000 / 706563706563) ∧
    -Real.log (500000000000 / 706563706563) ≤ (43225659 / 125000000) := by
  have h := checkLog_sound (w := (206563706563 / 1206563706563)) (n := 12)
    (lo := (345805271 / 1000000000)) (hi := (43225659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((706563706563 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(706563706563 / 500000000000) = 1/(500000000000 / 706563706563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2951 : Bounds (345805271 / 1000000000) (43225659 / 125000000) (Real.log (706563706563 / 500000000000)) := by
  have h := reflection_log_2951_neg
  have he : Real.log (706563706563 / 500000000000) = -Real.log (500000000000 / 706563706563) := by
    rw [show ((706563706563 / 500000000000) : ℝ) = ((500000000000 / 706563706563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2952_neg : (173005657 / 500000000) ≤ -Real.log (500000000000 / 706709303729) ∧
    -Real.log (500000000000 / 706709303729) ≤ (69202263 / 200000000) := by
  have h := checkLog_sound (w := (206709303729 / 1206709303729)) (n := 12)
    (lo := (173005657 / 500000000)) (hi := (69202263 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((706709303729 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(706709303729 / 500000000000) = 1/(500000000000 / 706709303729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2952 : Bounds (173005657 / 500000000) (69202263 / 200000000) (Real.log (706709303729 / 500000000000)) := by
  have h := reflection_log_2952_neg
  have he : Real.log (706709303729 / 500000000000) = -Real.log (500000000000 / 706709303729) := by
    rw [show ((706709303729 / 500000000000) : ℝ) = ((500000000000 / 706709303729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2953_neg : (79099807 / 500000000) ≤ -Real.log (5000 / 5857) ∧
    -Real.log (5000 / 5857) ≤ (31639923 / 200000000) := by
  have h := checkLog_sound (w := (857 / 10857)) (n := 12)
    (lo := (79099807 / 500000000)) (hi := (31639923 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5857 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5857 / 5000) = 1/(5000 / 5857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2953 : Bounds (79099807 / 500000000) (31639923 / 200000000) (Real.log (5857 / 5000)) := by
  have h := reflection_log_2953_neg
  have he : Real.log (5857 / 5000) = -Real.log (5000 / 5857) := by
    rw [show ((5857 / 5000) : ℝ) = ((5000 / 5857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2954_neg : (188017749 / 1000000000) ≤ -Real.log (4143 / 5000) ∧
    -Real.log (4143 / 5000) ≤ (752071 / 4000000) := by
  have h := checkLog_sound (w := (857 / 9143)) (n := 12)
    (lo := (188017749 / 1000000000)) (hi := (752071 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4143) = 1/(4143 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2954 : Bounds (-752071 / 4000000) (-188017749 / 1000000000) (Real.log (4143 / 5000)) := by
  have h := reflection_log_2954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2955_neg : (34277 / 200000000) ≤ -Real.log (5000000 / 5000857) ∧
    -Real.log (5000000 / 5000857) ≤ (85693 / 500000000) := by
  have h := checkLog_sound (w := (857 / 10000857)) (n := 12)
    (lo := (34277 / 200000000)) (hi := (85693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000857 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000857 / 5000000) = 1/(5000000 / 5000857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2955 : Bounds (34277 / 200000000) (85693 / 500000000) (Real.log (5000857 / 5000000)) := by
  have h := reflection_log_2955_neg
  have he : Real.log (5000857 / 5000000) = -Real.log (5000000 / 5000857) := by
    rw [show ((5000857 / 5000000) : ℝ) = ((5000000 / 5000857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2956_neg : (85707 / 500000000) ≤ -Real.log (4999143 / 5000000) ∧
    -Real.log (4999143 / 5000000) ≤ (34283 / 200000000) := by
  have h := checkLog_sound (w := (857 / 9999143)) (n := 12)
    (lo := (85707 / 500000000)) (hi := (34283 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999143) = 1/(4999143 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2956 : Bounds (-34283 / 200000000) (-85707 / 500000000) (Real.log (4999143 / 5000000)) := by
  have h := reflection_log_2956_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2957_neg : (41260279 / 500000000) ≤ -Real.log (1000000 / 1086021) ∧
    -Real.log (1000000 / 1086021) ≤ (82520559 / 1000000000) := by
  have h := checkLog_sound (w := (86021 / 2086021)) (n := 12)
    (lo := (41260279 / 500000000)) (hi := (82520559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086021 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1086021 / 1000000) = 1/(1000000 / 1086021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2957 : Bounds (41260279 / 500000000) (82520559 / 1000000000) (Real.log (1086021 / 1000000)) := by
  have h := reflection_log_2957_neg
  have he : Real.log (1086021 / 1000000) = -Real.log (1000000 / 1086021) := by
    rw [show ((1086021 / 1000000) : ℝ) = ((1000000 / 1086021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2958_neg : (89947683 / 1000000000) ≤ -Real.log (913979 / 1000000) ∧
    -Real.log (913979 / 1000000) ≤ (22486921 / 250000000) := by
  have h := checkLog_sound (w := (86021 / 1913979)) (n := 12)
    (lo := (89947683 / 1000000000)) (hi := (22486921 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 913979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 913979) = 1/(913979 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2958 : Bounds (-22486921 / 250000000) (-89947683 / 1000000000) (Real.log (913979 / 1000000)) := by
  have h := reflection_log_2958_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2959_neg : (82725873 / 1000000000) ≤ -Real.log (250000 / 271561) ∧
    -Real.log (250000 / 271561) ≤ (41362937 / 500000000) := by
  have h := checkLog_sound (w := (21561 / 521561)) (n := 12)
    (lo := (82725873 / 1000000000)) (hi := (41362937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271561 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271561 / 250000) = 1/(250000 / 271561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2959 : Bounds (82725873 / 1000000000) (41362937 / 500000000) (Real.log (271561 / 250000)) := by
  have h := reflection_log_2959_neg
  have he : Real.log (271561 / 250000) = -Real.log (250000 / 271561) := by
    rw [show ((271561 / 250000) : ℝ) = ((250000 / 271561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2960_neg : (90191701 / 1000000000) ≤ -Real.log (228439 / 250000) ∧
    -Real.log (228439 / 250000) ≤ (45095851 / 500000000) := by
  have h := checkLog_sound (w := (21561 / 478439)) (n := 12)
    (lo := (90191701 / 1000000000)) (hi := (45095851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228439) = 1/(228439 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2960 : Bounds (-45095851 / 500000000) (-90191701 / 1000000000) (Real.log (228439 / 250000)) := by
  have h := reflection_log_2960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2961_neg : (7465827 / 1000000000) ≤ -Real.log (62035123279 / 62500000000) ∧
    -Real.log (62035123279 / 62500000000) ≤ (1866457 / 250000000) := by
  have h := checkLog_sound (w := (464876721 / 124535123279)) (n := 12)
    (lo := (7465827 / 1000000000)) (hi := (1866457 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62035123279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62035123279) = 1/(62035123279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2961 : Bounds (-1866457 / 250000000) (-7465827 / 1000000000) (Real.log (62035123279 / 62500000000)) := by
  have h := reflection_log_2961_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2962_neg : (59417 / 8000000) ≤ -Real.log (992600387559 / 1000000000000) ∧
    -Real.log (992600387559 / 1000000000000) ≤ (3713563 / 500000000) := by
  have h := checkLog_sound (w := (7399612441 / 1992600387559)) (n := 12)
    (lo := (59417 / 8000000)) (hi := (3713563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992600387559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992600387559) = 1/(992600387559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2962 : Bounds (-3713563 / 500000000) (-59417 / 8000000) (Real.log (992600387559 / 1000000000000)) := by
  have h := reflection_log_2962_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2963_neg : (86234121 / 500000000) ≤ -Real.log (125000000000 / 148529260519) ∧
    -Real.log (125000000000 / 148529260519) ≤ (172468243 / 1000000000) := by
  have h := checkLog_sound (w := (23529260519 / 273529260519)) (n := 12)
    (lo := (86234121 / 500000000)) (hi := (172468243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148529260519 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148529260519 / 125000000000) = 1/(125000000000 / 148529260519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2963 : Bounds (86234121 / 500000000) (172468243 / 1000000000) (Real.log (148529260519 / 125000000000)) := by
  have h := reflection_log_2963_neg
  have he : Real.log (148529260519 / 125000000000) = -Real.log (125000000000 / 148529260519) := by
    rw [show ((148529260519 / 125000000000) : ℝ) = ((125000000000 / 148529260519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2964_neg : (6916703 / 40000000) ≤ -Real.log (100000000000 / 118876811753) ∧
    -Real.log (100000000000 / 118876811753) ≤ (21614697 / 125000000) := by
  have h := checkLog_sound (w := (18876811753 / 218876811753)) (n := 12)
    (lo := (6916703 / 40000000)) (hi := (21614697 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118876811753 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118876811753 / 100000000000) = 1/(100000000000 / 118876811753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2964 : Bounds (6916703 / 40000000) (21614697 / 125000000) (Real.log (118876811753 / 100000000000)) := by
  have h := reflection_log_2964_neg
  have he : Real.log (118876811753 / 100000000000) = -Real.log (100000000000 / 118876811753) := by
    rw [show ((118876811753 / 100000000000) : ℝ) = ((100000000000 / 118876811753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2965_neg : (173005657 / 500000000) ≤ -Real.log (31250000000 / 44169331483) ∧
    -Real.log (31250000000 / 44169331483) ≤ (69202263 / 200000000) := by
  have h := checkLog_sound (w := (12919331483 / 75419331483)) (n := 12)
    (lo := (173005657 / 500000000)) (hi := (69202263 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44169331483 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44169331483 / 31250000000) = 1/(31250000000 / 44169331483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2965 : Bounds (173005657 / 500000000) (69202263 / 200000000) (Real.log (44169331483 / 31250000000)) := by
  have h := reflection_log_2965_neg
  have he : Real.log (44169331483 / 31250000000) = -Real.log (31250000000 / 44169331483) := by
    rw [show ((44169331483 / 31250000000) : ℝ) = ((31250000000 / 44169331483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2966_neg : (86554341 / 250000000) ≤ -Real.log (500000000000 / 706854936037) ∧
    -Real.log (500000000000 / 706854936037) ≤ (69243473 / 200000000) := by
  have h := checkLog_sound (w := (206854936037 / 1206854936037)) (n := 12)
    (lo := (86554341 / 250000000)) (hi := (69243473 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((706854936037 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(706854936037 / 500000000000) = 1/(500000000000 / 706854936037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2966 : Bounds (86554341 / 250000000) (69243473 / 200000000) (Real.log (706854936037 / 500000000000)) := by
  have h := reflection_log_2966_neg
  have he : Real.log (706854936037 / 500000000000) = -Real.log (500000000000 / 706854936037) := by
    rw [show ((706854936037 / 500000000000) : ℝ) = ((500000000000 / 706854936037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2967_neg : (79142489 / 500000000) ≤ -Real.log (2000 / 2343) ∧
    -Real.log (2000 / 2343) ≤ (158284979 / 1000000000) := by
  have h := checkLog_sound (w := (343 / 4343)) (n := 12)
    (lo := (79142489 / 500000000)) (hi := (158284979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2343 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2343 / 2000) = 1/(2000 / 2343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2967 : Bounds (79142489 / 500000000) (158284979 / 1000000000) (Real.log (2343 / 2000)) := by
  have h := reflection_log_2967_neg
  have he : Real.log (2343 / 2000) = -Real.log (2000 / 2343) := by
    rw [show ((2343 / 2000) : ℝ) = ((2000 / 2343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2968_neg : (94069221 / 500000000) ≤ -Real.log (1657 / 2000) ∧
    -Real.log (1657 / 2000) ≤ (188138443 / 1000000000) := by
  have h := checkLog_sound (w := (343 / 3657)) (n := 12)
    (lo := (94069221 / 500000000)) (hi := (188138443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1657) = 1/(1657 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2968 : Bounds (-188138443 / 1000000000) (-94069221 / 500000000) (Real.log (1657 / 2000)) := by
  have h := reflection_log_2968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2969_neg : (34297 / 200000000) ≤ -Real.log (2000000 / 2000343) ∧
    -Real.log (2000000 / 2000343) ≤ (85743 / 500000000) := by
  have h := checkLog_sound (w := (343 / 4000343)) (n := 12)
    (lo := (34297 / 200000000)) (hi := (85743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000343 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000343 / 2000000) = 1/(2000000 / 2000343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2969 : Bounds (34297 / 200000000) (85743 / 500000000) (Real.log (2000343 / 2000000)) := by
  have h := reflection_log_2969_neg
  have he : Real.log (2000343 / 2000000) = -Real.log (2000000 / 2000343) := by
    rw [show ((2000343 / 2000000) : ℝ) = ((2000000 / 2000343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2970_neg : (85757 / 500000000) ≤ -Real.log (1999657 / 2000000) ∧
    -Real.log (1999657 / 2000000) ≤ (34303 / 200000000) := by
  have h := checkLog_sound (w := (343 / 3999657)) (n := 12)
    (lo := (85757 / 500000000)) (hi := (34303 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999657) = 1/(1999657 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2970 : Bounds (-34303 / 200000000) (-85757 / 500000000) (Real.log (1999657 / 2000000)) := by
  have h := reflection_log_2970_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2971_neg : (82567517 / 1000000000) ≤ -Real.log (125000 / 135759) ∧
    -Real.log (125000 / 135759) ≤ (41283759 / 500000000) := by
  have h := checkLog_sound (w := (10759 / 260759)) (n := 12)
    (lo := (82567517 / 1000000000)) (hi := (41283759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135759 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135759 / 125000) = 1/(125000 / 135759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2971 : Bounds (82567517 / 1000000000) (41283759 / 500000000) (Real.log (135759 / 125000)) := by
  have h := reflection_log_2971_neg
  have he : Real.log (135759 / 125000) = -Real.log (125000 / 135759) := by
    rw [show ((135759 / 125000) : ℝ) = ((125000 / 135759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2972_neg : (18000697 / 200000000) ≤ -Real.log (114241 / 125000) ∧
    -Real.log (114241 / 125000) ≤ (45001743 / 500000000) := by
  have h := checkLog_sound (w := (10759 / 239241)) (n := 12)
    (lo := (18000697 / 200000000)) (hi := (45001743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114241) = 1/(114241 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2972 : Bounds (-45001743 / 500000000) (-18000697 / 200000000) (Real.log (114241 / 125000)) := by
  have h := reflection_log_2972_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2973_neg : (82772823 / 1000000000) ≤ -Real.log (200000 / 217259) ∧
    -Real.log (200000 / 217259) ≤ (10346603 / 125000000) := by
  have h := checkLog_sound (w := (17259 / 417259)) (n := 12)
    (lo := (82772823 / 1000000000)) (hi := (10346603 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217259 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217259 / 200000) = 1/(200000 / 217259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2973 : Bounds (82772823 / 1000000000) (10346603 / 125000000) (Real.log (217259 / 200000)) := by
  have h := reflection_log_2973_neg
  have he : Real.log (217259 / 200000) = -Real.log (200000 / 217259) := by
    rw [show ((217259 / 200000) : ℝ) = ((200000 / 217259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2974_neg : (22561879 / 250000000) ≤ -Real.log (182741 / 200000) ∧
    -Real.log (182741 / 200000) ≤ (90247517 / 1000000000) := by
  have h := checkLog_sound (w := (17259 / 382741)) (n := 12)
    (lo := (22561879 / 250000000)) (hi := (90247517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182741) = 1/(182741 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2974 : Bounds (-90247517 / 1000000000) (-22561879 / 250000000) (Real.log (182741 / 200000)) := by
  have h := reflection_log_2974_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2975_neg : (7474693 / 1000000000) ≤ -Real.log (39702126919 / 40000000000) ∧
    -Real.log (39702126919 / 40000000000) ≤ (3737347 / 500000000) := by
  have h := checkLog_sound (w := (297873081 / 79702126919)) (n := 12)
    (lo := (7474693 / 1000000000)) (hi := (3737347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39702126919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39702126919) = 1/(39702126919 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2975 : Bounds (-3737347 / 500000000) (-7474693 / 1000000000) (Real.log (39702126919 / 40000000000)) := by
  have h := reflection_log_2975_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2976_neg : (7435967 / 1000000000) ≤ -Real.log (15509243919 / 15625000000) ∧
    -Real.log (15509243919 / 15625000000) ≤ (116187 / 15625000) := by
  have h := checkLog_sound (w := (115756081 / 31134243919)) (n := 12)
    (lo := (7435967 / 1000000000)) (hi := (116187 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15509243919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15509243919) = 1/(15509243919 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2976 : Bounds (-116187 / 15625000) (-7435967 / 1000000000) (Real.log (15509243919 / 15625000000)) := by
  have h := reflection_log_2976_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2977_neg : (86285501 / 500000000) ≤ -Real.log (25000000000 / 29708904859) ∧
    -Real.log (25000000000 / 29708904859) ≤ (172571003 / 1000000000) := by
  have h := checkLog_sound (w := (4708904859 / 54708904859)) (n := 12)
    (lo := (86285501 / 500000000)) (hi := (172571003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29708904859 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29708904859 / 25000000000) = 1/(25000000000 / 29708904859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2977 : Bounds (86285501 / 500000000) (172571003 / 1000000000) (Real.log (29708904859 / 25000000000)) := by
  have h := reflection_log_2977_neg
  have he : Real.log (29708904859 / 25000000000) = -Real.log (25000000000 / 29708904859) := by
    rw [show ((29708904859 / 25000000000) : ℝ) = ((25000000000 / 29708904859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2978_neg : (8651017 / 50000000) ≤ -Real.log (250000000000 / 297222571837) ∧
    -Real.log (250000000000 / 297222571837) ≤ (173020341 / 1000000000) := by
  have h := checkLog_sound (w := (47222571837 / 547222571837)) (n := 12)
    (lo := (8651017 / 50000000)) (hi := (173020341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297222571837 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297222571837 / 250000000000) = 1/(250000000000 / 297222571837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2978 : Bounds (8651017 / 50000000) (173020341 / 1000000000) (Real.log (297222571837 / 250000000000)) := by
  have h := reflection_log_2978_neg
  have he : Real.log (297222571837 / 250000000000) = -Real.log (250000000000 / 297222571837) := by
    rw [show ((297222571837 / 250000000000) : ℝ) = ((250000000000 / 297222571837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2979_neg : (86554341 / 250000000) ≤ -Real.log (125000000000 / 176713734009) ∧
    -Real.log (125000000000 / 176713734009) ≤ (69243473 / 200000000) := by
  have h := checkLog_sound (w := (51713734009 / 301713734009)) (n := 12)
    (lo := (86554341 / 250000000)) (hi := (69243473 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176713734009 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176713734009 / 125000000000) = 1/(125000000000 / 176713734009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2979 : Bounds (86554341 / 250000000) (69243473 / 200000000) (Real.log (176713734009 / 125000000000)) := by
  have h := reflection_log_2979_neg
  have he : Real.log (176713734009 / 125000000000) = -Real.log (125000000000 / 176713734009) := by
    rw [show ((176713734009 / 125000000000) : ℝ) = ((125000000000 / 176713734009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2980_neg : (346423421 / 1000000000) ≤ -Real.log (500000000000 / 707000603501) ∧
    -Real.log (500000000000 / 707000603501) ≤ (173211711 / 500000000) := by
  have h := checkLog_sound (w := (207000603501 / 1207000603501)) (n := 12)
    (lo := (346423421 / 1000000000)) (hi := (173211711 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707000603501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(707000603501 / 500000000000) = 1/(500000000000 / 707000603501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2980 : Bounds (346423421 / 1000000000) (173211711 / 500000000) (Real.log (707000603501 / 500000000000)) := by
  have h := reflection_log_2980_neg
  have he : Real.log (707000603501 / 500000000000) = -Real.log (500000000000 / 707000603501) := by
    rw [show ((707000603501 / 500000000000) : ℝ) = ((500000000000 / 707000603501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2981_neg : (31674067 / 200000000) ≤ -Real.log (2500 / 2929) ∧
    -Real.log (2500 / 2929) ≤ (4949073 / 31250000) := by
  have h := checkLog_sound (w := (429 / 5429)) (n := 12)
    (lo := (31674067 / 200000000)) (hi := (4949073 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2929 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2929 / 2500) = 1/(2500 / 2929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2981 : Bounds (31674067 / 200000000) (4949073 / 31250000) (Real.log (2929 / 2500)) := by
  have h := reflection_log_2981_neg
  have he : Real.log (2929 / 2500) = -Real.log (2500 / 2929) := by
    rw [show ((2929 / 2500) : ℝ) = ((2500 / 2929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2982_neg : (188259149 / 1000000000) ≤ -Real.log (2071 / 2500) ∧
    -Real.log (2071 / 2500) ≤ (3765183 / 20000000) := by
  have h := checkLog_sound (w := (429 / 4571)) (n := 12)
    (lo := (188259149 / 1000000000)) (hi := (3765183 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2071) = 1/(2071 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2982 : Bounds (-3765183 / 20000000) (-188259149 / 1000000000) (Real.log (2071 / 2500)) := by
  have h := reflection_log_2982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2983_neg : (34317 / 200000000) ≤ -Real.log (2500000 / 2500429) ∧
    -Real.log (2500000 / 2500429) ≤ (85793 / 500000000) := by
  have h := checkLog_sound (w := (429 / 5000429)) (n := 12)
    (lo := (34317 / 200000000)) (hi := (85793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500429 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500429 / 2500000) = 1/(2500000 / 2500429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2983 : Bounds (34317 / 200000000) (85793 / 500000000) (Real.log (2500429 / 2500000)) := by
  have h := reflection_log_2983_neg
  have he : Real.log (2500429 / 2500000) = -Real.log (2500000 / 2500429) := by
    rw [show ((2500429 / 2500000) : ℝ) = ((2500000 / 2500429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2984_neg : (85807 / 500000000) ≤ -Real.log (2499571 / 2500000) ∧
    -Real.log (2499571 / 2500000) ≤ (34323 / 200000000) := by
  have h := checkLog_sound (w := (429 / 4999571)) (n := 12)
    (lo := (85807 / 500000000)) (hi := (34323 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499571) = 1/(2499571 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2984 : Bounds (-34323 / 200000000) (-85807 / 500000000) (Real.log (2499571 / 2500000)) := by
  have h := reflection_log_2984_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2985_neg : (41307237 / 500000000) ≤ -Real.log (1000000 / 1086123) ∧
    -Real.log (1000000 / 1086123) ≤ (3304579 / 40000000) := by
  have h := checkLog_sound (w := (86123 / 2086123)) (n := 12)
    (lo := (41307237 / 500000000)) (hi := (3304579 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086123 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1086123 / 1000000) = 1/(1000000 / 1086123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2985 : Bounds (41307237 / 500000000) (3304579 / 40000000) (Real.log (1086123 / 1000000)) := by
  have h := reflection_log_2985_neg
  have he : Real.log (1086123 / 1000000) = -Real.log (1000000 / 1086123) := by
    rw [show ((1086123 / 1000000) : ℝ) = ((1000000 / 1086123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2986_neg : (90059289 / 1000000000) ≤ -Real.log (913877 / 1000000) ∧
    -Real.log (913877 / 1000000) ≤ (9005929 / 100000000) := by
  have h := checkLog_sound (w := (86123 / 1913877)) (n := 12)
    (lo := (90059289 / 1000000000)) (hi := (9005929 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 913877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 913877) = 1/(913877 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2986 : Bounds (-9005929 / 100000000) (-90059289 / 1000000000) (Real.log (913877 / 1000000)) := by
  have h := reflection_log_2986_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2987_neg : (1656377 / 20000000) ≤ -Real.log (200000 / 217269) ∧
    -Real.log (200000 / 217269) ≤ (82818851 / 1000000000) := by
  have h := checkLog_sound (w := (17269 / 417269)) (n := 12)
    (lo := (1656377 / 20000000)) (hi := (82818851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217269 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217269 / 200000) = 1/(200000 / 217269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2987 : Bounds (1656377 / 20000000) (82818851 / 1000000000) (Real.log (217269 / 200000)) := by
  have h := reflection_log_2987_neg
  have he : Real.log (217269 / 200000) = -Real.log (200000 / 217269) := by
    rw [show ((217269 / 200000) : ℝ) = ((200000 / 217269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2988_neg : (564389 / 6250000) ≤ -Real.log (182731 / 200000) ∧
    -Real.log (182731 / 200000) ≤ (90302241 / 1000000000) := by
  have h := checkLog_sound (w := (17269 / 382731)) (n := 12)
    (lo := (564389 / 6250000)) (hi := (90302241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182731) = 1/(182731 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2988 : Bounds (-90302241 / 1000000000) (-564389 / 6250000) (Real.log (182731 / 200000)) := by
  have h := reflection_log_2988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2989_neg : (7483389 / 1000000000) ≤ -Real.log (39701781639 / 40000000000) ∧
    -Real.log (39701781639 / 40000000000) ≤ (748339 / 100000000) := by
  have h := checkLog_sound (w := (298218361 / 79701781639)) (n := 12)
    (lo := (7483389 / 1000000000)) (hi := (748339 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39701781639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39701781639) = 1/(39701781639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2989 : Bounds (-748339 / 100000000) (-7483389 / 1000000000) (Real.log (39701781639 / 40000000000)) := by
  have h := reflection_log_2989_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2990_neg : (1488963 / 200000000) ≤ -Real.log (992582828871 / 1000000000000) ∧
    -Real.log (992582828871 / 1000000000000) ≤ (465301 / 62500000) := by
  have h := checkLog_sound (w := (7417171129 / 1992582828871)) (n := 12)
    (lo := (1488963 / 200000000)) (hi := (465301 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992582828871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992582828871) = 1/(992582828871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2990 : Bounds (-465301 / 62500000) (-1488963 / 200000000) (Real.log (992582828871 / 1000000000000)) := by
  have h := reflection_log_2990_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2991_neg : (43168441 / 250000000) ≤ -Real.log (500000000000 / 594239159099) ∧
    -Real.log (500000000000 / 594239159099) ≤ (34534753 / 200000000) := by
  have h := checkLog_sound (w := (94239159099 / 1094239159099)) (n := 12)
    (lo := (43168441 / 250000000)) (hi := (34534753 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594239159099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594239159099 / 500000000000) = 1/(500000000000 / 594239159099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2991 : Bounds (43168441 / 250000000) (34534753 / 200000000) (Real.log (594239159099 / 500000000000)) := by
  have h := reflection_log_2991_neg
  have he : Real.log (594239159099 / 500000000000) = -Real.log (500000000000 / 594239159099) := by
    rw [show ((594239159099 / 500000000000) : ℝ) = ((500000000000 / 594239159099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2992_neg : (173121091 / 1000000000) ≤ -Real.log (25000000000 / 29725251873) ∧
    -Real.log (25000000000 / 29725251873) ≤ (43280273 / 250000000) := by
  have h := checkLog_sound (w := (4725251873 / 54725251873)) (n := 12)
    (lo := (173121091 / 1000000000)) (hi := (43280273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29725251873 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29725251873 / 25000000000) = 1/(25000000000 / 29725251873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2992 : Bounds (173121091 / 1000000000) (43280273 / 250000000) (Real.log (29725251873 / 25000000000)) := by
  have h := reflection_log_2992_neg
  have he : Real.log (29725251873 / 25000000000) = -Real.log (25000000000 / 29725251873) := by
    rw [show ((29725251873 / 25000000000) : ℝ) = ((25000000000 / 29725251873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2993_neg : (346423421 / 1000000000) ≤ -Real.log (1000000000 / 1414001207) ∧
    -Real.log (1000000000 / 1414001207) ≤ (173211711 / 500000000) := by
  have h := checkLog_sound (w := (414001207 / 2414001207)) (n := 12)
    (lo := (346423421 / 1000000000)) (hi := (173211711 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1414001207 / 1000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1414001207 / 1000000000) = 1/(1000000000 / 1414001207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2993 : Bounds (346423421 / 1000000000) (173211711 / 500000000) (Real.log (1414001207 / 1000000000)) := by
  have h := reflection_log_2993_neg
  have he : Real.log (1414001207 / 1000000000) = -Real.log (1000000000 / 1414001207) := by
    rw [show ((1414001207 / 1000000000) : ℝ) = ((1000000000 / 1414001207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2994_neg : (69325897 / 200000000) ≤ -Real.log (500000000000 / 707146306133) ∧
    -Real.log (500000000000 / 707146306133) ≤ (173314743 / 500000000) := by
  have h := checkLog_sound (w := (207146306133 / 1207146306133)) (n := 12)
    (lo := (69325897 / 200000000)) (hi := (173314743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707146306133 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(707146306133 / 500000000000) = 1/(500000000000 / 707146306133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2994 : Bounds (69325897 / 200000000) (173314743 / 500000000) (Real.log (707146306133 / 500000000000)) := by
  have h := reflection_log_2994_neg
  have he : Real.log (707146306133 / 500000000000) = -Real.log (500000000000 / 707146306133) := by
    rw [show ((707146306133 / 500000000000) : ℝ) = ((500000000000 / 707146306133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2995_neg : (31691137 / 200000000) ≤ -Real.log (10000 / 11717) ∧
    -Real.log (10000 / 11717) ≤ (79227843 / 500000000) := by
  have h := checkLog_sound (w := (1717 / 21717)) (n := 12)
    (lo := (31691137 / 200000000)) (hi := (79227843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11717 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11717 / 10000) = 1/(10000 / 11717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2995 : Bounds (31691137 / 200000000) (79227843 / 500000000) (Real.log (11717 / 10000)) := by
  have h := reflection_log_2995_neg
  have he : Real.log (11717 / 10000) = -Real.log (10000 / 11717) := by
    rw [show ((11717 / 10000) : ℝ) = ((10000 / 11717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2996_neg : (188379871 / 1000000000) ≤ -Real.log (8283 / 10000) ∧
    -Real.log (8283 / 10000) ≤ (5886871 / 31250000) := by
  have h := checkLog_sound (w := (1717 / 18283)) (n := 12)
    (lo := (188379871 / 1000000000)) (hi := (5886871 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8283) = 1/(8283 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2996 : Bounds (-5886871 / 31250000) (-188379871 / 1000000000) (Real.log (8283 / 10000)) := by
  have h := reflection_log_2996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2997_neg : (34337 / 200000000) ≤ -Real.log (10000000 / 10001717) ∧
    -Real.log (10000000 / 10001717) ≤ (85843 / 500000000) := by
  have h := checkLog_sound (w := (1717 / 20001717)) (n := 12)
    (lo := (34337 / 200000000)) (hi := (85843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001717 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001717 / 10000000) = 1/(10000000 / 10001717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2997 : Bounds (34337 / 200000000) (85843 / 500000000) (Real.log (10001717 / 10000000)) := by
  have h := reflection_log_2997_neg
  have he : Real.log (10001717 / 10000000) = -Real.log (10000000 / 10001717) := by
    rw [show ((10001717 / 10000000) : ℝ) = ((10000000 / 10001717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2998_neg : (85857 / 500000000) ≤ -Real.log (9998283 / 10000000) ∧
    -Real.log (9998283 / 10000000) ≤ (34343 / 200000000) := by
  have h := checkLog_sound (w := (1717 / 19998283)) (n := 12)
    (lo := (85857 / 500000000)) (hi := (34343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998283) = 1/(9998283 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2998 : Bounds (-34343 / 200000000) (-85857 / 500000000) (Real.log (9998283 / 10000000)) := by
  have h := reflection_log_2998_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2999_neg : (82661429 / 1000000000) ≤ -Real.log (500000 / 543087) ∧
    -Real.log (500000 / 543087) ≤ (8266143 / 100000000) := by
  have h := checkLog_sound (w := (43087 / 1043087)) (n := 12)
    (lo := (82661429 / 1000000000)) (hi := (8266143 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543087 / 500000) = 1/(500000 / 543087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2999 : Bounds (82661429 / 1000000000) (8266143 / 100000000) (Real.log (543087 / 500000)) := by
  have h := reflection_log_2999_neg
  have he : Real.log (543087 / 500000) = -Real.log (500000 / 543087) := by
    rw [show ((543087 / 500000) : ℝ) = ((500000 / 543087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3000_neg : (90115097 / 1000000000) ≤ -Real.log (456913 / 500000) ∧
    -Real.log (456913 / 500000) ≤ (45057549 / 500000000) := by
  have h := checkLog_sound (w := (43087 / 956913)) (n := 12)
    (lo := (90115097 / 1000000000)) (hi := (45057549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456913) = 1/(456913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3000 : Bounds (-45057549 / 500000000) (-90115097 / 1000000000) (Real.log (456913 / 500000)) := by
  have h := reflection_log_3000_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3001_neg : (16573159 / 200000000) ≤ -Real.log (250000 / 271599) ∧
    -Real.log (250000 / 271599) ≤ (20716449 / 250000000) := by
  have h := checkLog_sound (w := (21599 / 521599)) (n := 12)
    (lo := (16573159 / 200000000)) (hi := (20716449 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271599 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271599 / 250000) = 1/(250000 / 271599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3001 : Bounds (16573159 / 200000000) (20716449 / 250000000) (Real.log (271599 / 250000)) := by
  have h := reflection_log_3001_neg
  have he : Real.log (271599 / 250000) = -Real.log (250000 / 271599) := by
    rw [show ((271599 / 250000) : ℝ) = ((250000 / 271599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3002_neg : (90358061 / 1000000000) ≤ -Real.log (228401 / 250000) ∧
    -Real.log (228401 / 250000) ≤ (45179031 / 500000000) := by
  have h := checkLog_sound (w := (21599 / 478401)) (n := 12)
    (lo := (90358061 / 1000000000)) (hi := (45179031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228401) = 1/(228401 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3002 : Bounds (-45179031 / 500000000) (-90358061 / 1000000000) (Real.log (228401 / 250000)) := by
  have h := reflection_log_3002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3003_neg : (1498453 / 200000000) ≤ -Real.log (62033483199 / 62500000000) ∧
    -Real.log (62033483199 / 62500000000) ≤ (3746133 / 500000000) := by
  have h := checkLog_sound (w := (466516801 / 124533483199)) (n := 12)
    (lo := (1498453 / 200000000)) (hi := (3746133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62033483199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62033483199) = 1/(62033483199 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3003 : Bounds (-3746133 / 500000000) (-1498453 / 200000000) (Real.log (62033483199 / 62500000000)) := by
  have h := reflection_log_3003_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3004_neg : (7453667 / 1000000000) ≤ -Real.log (248143510431 / 250000000000) ∧
    -Real.log (248143510431 / 250000000000) ≤ (1863417 / 250000000) := by
  have h := checkLog_sound (w := (1856489569 / 498143510431)) (n := 12)
    (lo := (7453667 / 1000000000)) (hi := (1863417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248143510431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248143510431) = 1/(248143510431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3004 : Bounds (-1863417 / 250000000) (-7453667 / 1000000000) (Real.log (248143510431 / 250000000000)) := by
  have h := reflection_log_3004_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3005_neg : (172776527 / 1000000000) ≤ -Real.log (500000000000 / 594300227833) ∧
    -Real.log (500000000000 / 594300227833) ≤ (10798533 / 62500000) := by
  have h := checkLog_sound (w := (94300227833 / 1094300227833)) (n := 12)
    (lo := (172776527 / 1000000000)) (hi := (10798533 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594300227833 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594300227833 / 500000000000) = 1/(500000000000 / 594300227833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3005 : Bounds (172776527 / 1000000000) (10798533 / 62500000) (Real.log (594300227833 / 500000000000)) := by
  have h := reflection_log_3005_neg
  have he : Real.log (594300227833 / 500000000000) = -Real.log (500000000000 / 594300227833) := by
    rw [show ((594300227833 / 500000000000) : ℝ) = ((500000000000 / 594300227833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3006_neg : (173223857 / 1000000000) ≤ -Real.log (125000000000 / 148641533969) ∧
    -Real.log (125000000000 / 148641533969) ≤ (86611929 / 500000000) := by
  have h := checkLog_sound (w := (23641533969 / 273641533969)) (n := 12)
    (lo := (173223857 / 1000000000)) (hi := (86611929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148641533969 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148641533969 / 125000000000) = 1/(125000000000 / 148641533969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3006 : Bounds (173223857 / 1000000000) (86611929 / 500000000) (Real.log (148641533969 / 125000000000)) := by
  have h := reflection_log_3006_neg
  have he : Real.log (148641533969 / 125000000000) = -Real.log (125000000000 / 148641533969) := by
    rw [show ((148641533969 / 125000000000) : ℝ) = ((125000000000 / 148641533969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3007_neg : (69325897 / 200000000) ≤ -Real.log (125000000000 / 176786576533) ∧
    -Real.log (125000000000 / 176786576533) ≤ (173314743 / 500000000) := by
  have h := checkLog_sound (w := (51786576533 / 301786576533)) (n := 12)
    (lo := (69325897 / 200000000)) (hi := (173314743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176786576533 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176786576533 / 125000000000) = 1/(125000000000 / 176786576533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3007 : Bounds (69325897 / 200000000) (173314743 / 500000000) (Real.log (176786576533 / 125000000000)) := by
  have h := reflection_log_3007_neg
  have he : Real.log (176786576533 / 125000000000) = -Real.log (125000000000 / 176786576533) := by
    rw [show ((176786576533 / 125000000000) : ℝ) = ((125000000000 / 176786576533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
