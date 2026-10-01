import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6208_neg : (386563 / 40000000) ≤ -Real.log (990382471239 / 1000000000000) ∧
    -Real.log (990382471239 / 1000000000000) ≤ (2416019 / 250000000) := by
  have h := checkLog_sound (w := (9617528761 / 1990382471239)) (n := 12)
    (lo := (386563 / 40000000)) (hi := (2416019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990382471239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990382471239) = 1/(990382471239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6208 : Bounds (-2416019 / 250000000) (-386563 / 40000000) (Real.log (990382471239 / 1000000000000)) := by
  have h := reflection_log_6208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6209_neg : (9615617 / 1000000000) ≤ -Real.log (967217251 / 976562500) ∧
    -Real.log (967217251 / 976562500) ≤ (4807809 / 500000000) := by
  have h := checkLog_sound (w := (9345249 / 1943779751)) (n := 12)
    (lo := (9615617 / 1000000000)) (hi := (4807809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 967217251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 967217251) = 1/(967217251 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6209 : Bounds (-4807809 / 500000000) (-9615617 / 1000000000) (Real.log (967217251 / 976562500)) := by
  have h := reflection_log_6209_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6210_neg : (98137847 / 500000000) ≤ -Real.log (250000000000 / 304215585429) ∧
    -Real.log (250000000000 / 304215585429) ≤ (39255139 / 200000000) := by
  have h := checkLog_sound (w := (54215585429 / 554215585429)) (n := 12)
    (lo := (98137847 / 500000000)) (hi := (39255139 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304215585429 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304215585429 / 250000000000) = 1/(250000000000 / 304215585429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6210 : Bounds (98137847 / 500000000) (39255139 / 200000000) (Real.log (304215585429 / 250000000000)) := by
  have h := reflection_log_6210_neg
  have he : Real.log (304215585429 / 250000000000) = -Real.log (250000000000 / 304215585429) := by
    rw [show ((304215585429 / 250000000000) : ℝ) = ((250000000000 / 304215585429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6211_neg : (196770441 / 1000000000) ≤ -Real.log (250000000000 / 304366132221) ∧
    -Real.log (250000000000 / 304366132221) ≤ (98385221 / 500000000) := by
  have h := checkLog_sound (w := (54366132221 / 554366132221)) (n := 12)
    (lo := (196770441 / 1000000000)) (hi := (98385221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304366132221 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304366132221 / 250000000000) = 1/(250000000000 / 304366132221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6211 : Bounds (196770441 / 1000000000) (98385221 / 500000000) (Real.log (304366132221 / 250000000000)) := by
  have h := reflection_log_6211_neg
  have he : Real.log (304366132221 / 250000000000) = -Real.log (250000000000 / 304366132221) := by
    rw [show ((304366132221 / 250000000000) : ℝ) = ((250000000000 / 304366132221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6212_neg : (98504941 / 250000000) ≤ -Real.log (100000000000 / 148292985723) ∧
    -Real.log (100000000000 / 148292985723) ≤ (78803953 / 200000000) := by
  have h := checkLog_sound (w := (48292985723 / 248292985723)) (n := 12)
    (lo := (98504941 / 250000000)) (hi := (78803953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148292985723 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148292985723 / 100000000000) = 1/(100000000000 / 148292985723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6212 : Bounds (98504941 / 250000000) (78803953 / 200000000) (Real.log (148292985723 / 100000000000)) := by
  have h := reflection_log_6212_neg
  have he : Real.log (148292985723 / 100000000000) = -Real.log (100000000000 / 148292985723) := by
    rw [show ((148292985723 / 100000000000) : ℝ) = ((100000000000 / 148292985723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6213_neg : (394227631 / 1000000000) ≤ -Real.log (500000000000 / 741619071269) ∧
    -Real.log (500000000000 / 741619071269) ≤ (24639227 / 62500000) := by
  have h := checkLog_sound (w := (241619071269 / 1241619071269)) (n := 12)
    (lo := (394227631 / 1000000000)) (hi := (24639227 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741619071269 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741619071269 / 500000000000) = 1/(500000000000 / 741619071269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6213 : Bounds (394227631 / 1000000000) (24639227 / 62500000) (Real.log (741619071269 / 500000000000)) := by
  have h := reflection_log_6213_neg
  have he : Real.log (741619071269 / 500000000000) = -Real.log (500000000000 / 741619071269) := by
    rw [show ((741619071269 / 500000000000) : ℝ) = ((500000000000 / 741619071269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6214_neg : (177895107 / 1000000000) ≤ -Real.log (10000 / 11947) ∧
    -Real.log (10000 / 11947) ≤ (44473777 / 250000000) := by
  have h := checkLog_sound (w := (1947 / 21947)) (n := 12)
    (lo := (177895107 / 1000000000)) (hi := (44473777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11947 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11947 / 10000) = 1/(10000 / 11947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6214 : Bounds (177895107 / 1000000000) (44473777 / 250000000) (Real.log (11947 / 10000)) := by
  have h := reflection_log_6214_neg
  have he : Real.log (11947 / 10000) = -Real.log (10000 / 11947) := by
    rw [show ((11947 / 10000) : ℝ) = ((10000 / 11947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6215_neg : (541351 / 2500000) ≤ -Real.log (8053 / 10000) ∧
    -Real.log (8053 / 10000) ≤ (216540401 / 1000000000) := by
  have h := checkLog_sound (w := (1947 / 18053)) (n := 12)
    (lo := (541351 / 2500000)) (hi := (216540401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8053) = 1/(8053 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6215 : Bounds (-216540401 / 1000000000) (-541351 / 2500000) (Real.log (8053 / 10000)) := by
  have h := reflection_log_6215_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6216_neg : (194681 / 1000000000) ≤ -Real.log (10000000 / 10001947) ∧
    -Real.log (10000000 / 10001947) ≤ (97341 / 500000000) := by
  have h := checkLog_sound (w := (1947 / 20001947)) (n := 12)
    (lo := (194681 / 1000000000)) (hi := (97341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001947 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001947 / 10000000) = 1/(10000000 / 10001947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6216 : Bounds (194681 / 1000000000) (97341 / 500000000) (Real.log (10001947 / 10000000)) := by
  have h := reflection_log_6216_neg
  have he : Real.log (10001947 / 10000000) = -Real.log (10000000 / 10001947) := by
    rw [show ((10001947 / 10000000) : ℝ) = ((10000000 / 10001947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6217_neg : (97359 / 500000000) ≤ -Real.log (9998053 / 10000000) ∧
    -Real.log (9998053 / 10000000) ≤ (194719 / 1000000000) := by
  have h := checkLog_sound (w := (1947 / 19998053)) (n := 12)
    (lo := (97359 / 500000000)) (hi := (194719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998053) = 1/(9998053 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6217 : Bounds (-194719 / 1000000000) (-97359 / 500000000) (Real.log (9998053 / 10000000)) := by
  have h := reflection_log_6217_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6218_neg : (93376493 / 1000000000) ≤ -Real.log (8000 / 8783) ∧
    -Real.log (8000 / 8783) ≤ (46688247 / 500000000) := by
  have h := checkLog_sound (w := (783 / 16783)) (n := 12)
    (lo := (93376493 / 1000000000)) (hi := (46688247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8783 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8783 / 8000) = 1/(8000 / 8783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6218 : Bounds (93376493 / 1000000000) (46688247 / 500000000) (Real.log (8783 / 8000)) := by
  have h := reflection_log_6218_neg
  have he : Real.log (8783 / 8000) = -Real.log (8000 / 8783) := by
    rw [show ((8783 / 8000) : ℝ) = ((8000 / 8783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6219_neg : (103002187 / 1000000000) ≤ -Real.log (7217 / 8000) ∧
    -Real.log (7217 / 8000) ≤ (25750547 / 250000000) := by
  have h := checkLog_sound (w := (783 / 15217)) (n := 12)
    (lo := (103002187 / 1000000000)) (hi := (25750547 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 7217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 7217) = 1/(7217 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6219 : Bounds (-25750547 / 250000000) (-103002187 / 1000000000) (Real.log (7217 / 8000)) := by
  have h := reflection_log_6219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6220_neg : (46799813 / 500000000) ≤ -Real.log (25000 / 27453) ∧
    -Real.log (25000 / 27453) ≤ (93599627 / 1000000000) := by
  have h := checkLog_sound (w := (2453 / 52453)) (n := 12)
    (lo := (46799813 / 500000000)) (hi := (93599627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27453 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27453 / 25000) = 1/(25000 / 27453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6220 : Bounds (46799813 / 500000000) (93599627 / 1000000000) (Real.log (27453 / 25000)) := by
  have h := reflection_log_6220_neg
  have he : Real.log (27453 / 25000) = -Real.log (25000 / 27453) := by
    rw [show ((27453 / 25000) : ℝ) = ((25000 / 27453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6221_neg : (20654761 / 200000000) ≤ -Real.log (22547 / 25000) ∧
    -Real.log (22547 / 25000) ≤ (51636903 / 500000000) := by
  have h := checkLog_sound (w := (2453 / 47547)) (n := 12)
    (lo := (20654761 / 200000000)) (hi := (51636903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22547) = 1/(22547 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6221 : Bounds (-51636903 / 500000000) (-20654761 / 200000000) (Real.log (22547 / 25000)) := by
  have h := reflection_log_6221_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6222_neg : (4837089 / 500000000) ≤ -Real.log (618982791 / 625000000) ∧
    -Real.log (618982791 / 625000000) ≤ (9674179 / 1000000000) := by
  have h := checkLog_sound (w := (6017209 / 1243982791)) (n := 12)
    (lo := (4837089 / 500000000)) (hi := (9674179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 618982791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 618982791) = 1/(618982791 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6222 : Bounds (-9674179 / 1000000000) (-4837089 / 500000000) (Real.log (618982791 / 625000000)) := by
  have h := reflection_log_6222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6223_neg : (4812847 / 500000000) ≤ -Real.log (63386911 / 64000000) ∧
    -Real.log (63386911 / 64000000) ≤ (1925139 / 200000000) := by
  have h := checkLog_sound (w := (613089 / 127386911)) (n := 12)
    (lo := (4812847 / 500000000)) (hi := (1925139 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64000000 / 63386911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64000000 / 63386911) = 1/(63386911 / 64000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6223 : Bounds (-1925139 / 200000000) (-4812847 / 500000000) (Real.log (63386911 / 64000000)) := by
  have h := reflection_log_6223_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6224_neg : (4909467 / 25000000) ≤ -Real.log (500000000000 / 608493834003) ∧
    -Real.log (500000000000 / 608493834003) ≤ (196378681 / 1000000000) := by
  have h := checkLog_sound (w := (108493834003 / 1108493834003)) (n := 12)
    (lo := (4909467 / 25000000)) (hi := (196378681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608493834003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608493834003 / 500000000000) = 1/(500000000000 / 608493834003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6224 : Bounds (4909467 / 25000000) (196378681 / 1000000000) (Real.log (608493834003 / 500000000000)) := by
  have h := reflection_log_6224_neg
  have he : Real.log (608493834003 / 500000000000) = -Real.log (500000000000 / 608493834003) := by
    rw [show ((608493834003 / 500000000000) : ℝ) = ((500000000000 / 608493834003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6225_neg : (24609179 / 125000000) ≤ -Real.log (125000000000 / 152198740409) ∧
    -Real.log (125000000000 / 152198740409) ≤ (196873433 / 1000000000) := by
  have h := checkLog_sound (w := (27198740409 / 277198740409)) (n := 12)
    (lo := (24609179 / 125000000)) (hi := (196873433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152198740409 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152198740409 / 125000000000) = 1/(125000000000 / 152198740409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6225 : Bounds (24609179 / 125000000) (196873433 / 1000000000) (Real.log (152198740409 / 125000000000)) := by
  have h := reflection_log_6225_neg
  have he : Real.log (152198740409 / 125000000000) = -Real.log (125000000000 / 152198740409) := by
    rw [show ((152198740409 / 125000000000) : ℝ) = ((125000000000 / 152198740409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6226_neg : (394227631 / 1000000000) ≤ -Real.log (125000000000 / 185404767817) ∧
    -Real.log (125000000000 / 185404767817) ≤ (24639227 / 62500000) := by
  have h := checkLog_sound (w := (60404767817 / 310404767817)) (n := 12)
    (lo := (394227631 / 1000000000)) (hi := (24639227 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185404767817 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185404767817 / 125000000000) = 1/(125000000000 / 185404767817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6226 : Bounds (394227631 / 1000000000) (24639227 / 62500000) (Real.log (185404767817 / 125000000000)) := by
  have h := reflection_log_6226_neg
  have he : Real.log (185404767817 / 125000000000) = -Real.log (125000000000 / 185404767817) := by
    rw [show ((185404767817 / 125000000000) : ℝ) = ((125000000000 / 185404767817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6227_neg : (98608877 / 250000000) ≤ -Real.log (100000000000 / 148354650441) ∧
    -Real.log (100000000000 / 148354650441) ≤ (394435509 / 1000000000) := by
  have h := checkLog_sound (w := (48354650441 / 248354650441)) (n := 12)
    (lo := (98608877 / 250000000)) (hi := (394435509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148354650441 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148354650441 / 100000000000) = 1/(100000000000 / 148354650441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6227 : Bounds (98608877 / 250000000) (394435509 / 1000000000) (Real.log (148354650441 / 100000000000)) := by
  have h := reflection_log_6227_neg
  have he : Real.log (148354650441 / 100000000000) = -Real.log (100000000000 / 148354650441) := by
    rw [show ((148354650441 / 100000000000) : ℝ) = ((100000000000 / 148354650441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6228_neg : (177978807 / 1000000000) ≤ -Real.log (2500 / 2987) ∧
    -Real.log (2500 / 2987) ≤ (22247351 / 125000000) := by
  have h := checkLog_sound (w := (487 / 5487)) (n := 12)
    (lo := (177978807 / 1000000000)) (hi := (22247351 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2987 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2987 / 2500) = 1/(2500 / 2987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6228 : Bounds (177978807 / 1000000000) (22247351 / 125000000) (Real.log (2987 / 2500)) := by
  have h := reflection_log_6228_neg
  have he : Real.log (2987 / 2500) = -Real.log (2500 / 2987) := by
    rw [show ((2987 / 2500) : ℝ) = ((2500 / 2987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6229_neg : (43332917 / 200000000) ≤ -Real.log (2013 / 2500) ∧
    -Real.log (2013 / 2500) ≤ (108332293 / 500000000) := by
  have h := checkLog_sound (w := (487 / 4513)) (n := 12)
    (lo := (43332917 / 200000000)) (hi := (108332293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2013) = 1/(2013 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6229 : Bounds (-108332293 / 500000000) (-43332917 / 200000000) (Real.log (2013 / 2500)) := by
  have h := reflection_log_6229_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6230_neg : (194781 / 1000000000) ≤ -Real.log (2500000 / 2500487) ∧
    -Real.log (2500000 / 2500487) ≤ (97391 / 500000000) := by
  have h := checkLog_sound (w := (487 / 5000487)) (n := 12)
    (lo := (194781 / 1000000000)) (hi := (97391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500487 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500487 / 2500000) = 1/(2500000 / 2500487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6230 : Bounds (194781 / 1000000000) (97391 / 500000000) (Real.log (2500487 / 2500000)) := by
  have h := reflection_log_6230_neg
  have he : Real.log (2500487 / 2500000) = -Real.log (2500000 / 2500487) := by
    rw [show ((2500487 / 2500000) : ℝ) = ((2500000 / 2500487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6231_neg : (97409 / 500000000) ≤ -Real.log (2499513 / 2500000) ∧
    -Real.log (2499513 / 2500000) ≤ (194819 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 4999513)) (n := 12)
    (lo := (97409 / 500000000)) (hi := (194819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499513) = 1/(2499513 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6231 : Bounds (-194819 / 1000000000) (-97409 / 500000000) (Real.log (2499513 / 2500000)) := by
  have h := reflection_log_6231_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6232_neg : (18684589 / 200000000) ≤ -Real.log (500000 / 548963) ∧
    -Real.log (500000 / 548963) ≤ (46711473 / 500000000) := by
  have h := checkLog_sound (w := (48963 / 1048963)) (n := 12)
    (lo := (18684589 / 200000000)) (hi := (46711473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548963 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548963 / 500000) = 1/(500000 / 548963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6232 : Bounds (18684589 / 200000000) (46711473 / 500000000) (Real.log (548963 / 500000)) := by
  have h := reflection_log_6232_neg
  have he : Real.log (548963 / 500000) = -Real.log (500000 / 548963) := by
    rw [show ((548963 / 500000) : ℝ) = ((500000 / 548963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6233_neg : (51529361 / 500000000) ≤ -Real.log (451037 / 500000) ∧
    -Real.log (451037 / 500000) ≤ (103058723 / 1000000000) := by
  have h := checkLog_sound (w := (48963 / 951037)) (n := 12)
    (lo := (51529361 / 500000000)) (hi := (103058723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451037) = 1/(451037 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6233 : Bounds (-103058723 / 1000000000) (-51529361 / 500000000) (Real.log (451037 / 500000)) := by
  have h := reflection_log_6233_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6234_neg : (23411517 / 250000000) ≤ -Real.log (1000000 / 1098171) ∧
    -Real.log (1000000 / 1098171) ≤ (93646069 / 1000000000) := by
  have h := checkLog_sound (w := (98171 / 2098171)) (n := 12)
    (lo := (23411517 / 250000000)) (hi := (93646069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098171 / 1000000) = 1/(1000000 / 1098171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6234 : Bounds (23411517 / 250000000) (93646069 / 1000000000) (Real.log (1098171 / 1000000)) := by
  have h := reflection_log_6234_neg
  have he : Real.log (1098171 / 1000000) = -Real.log (1000000 / 1098171) := by
    rw [show ((1098171 / 1000000) : ℝ) = ((1000000 / 1098171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6235_neg : (20666071 / 200000000) ≤ -Real.log (901829 / 1000000) ∧
    -Real.log (901829 / 1000000) ≤ (25832589 / 250000000) := by
  have h := checkLog_sound (w := (98171 / 1901829)) (n := 12)
    (lo := (20666071 / 200000000)) (hi := (25832589 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901829) = 1/(901829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6235 : Bounds (-25832589 / 250000000) (-20666071 / 200000000) (Real.log (901829 / 1000000)) := by
  have h := reflection_log_6235_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6236_neg : (4842143 / 500000000) ≤ -Real.log (990362454759 / 1000000000000) ∧
    -Real.log (990362454759 / 1000000000000) ≤ (9684287 / 1000000000) := by
  have h := checkLog_sound (w := (9637545241 / 1990362454759)) (n := 12)
    (lo := (4842143 / 500000000)) (hi := (9684287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990362454759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990362454759) = 1/(990362454759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6236 : Bounds (-9684287 / 1000000000) (-4842143 / 500000000) (Real.log (990362454759 / 1000000000000)) := by
  have h := reflection_log_6236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6237_neg : (150559 / 15625000) ≤ -Real.log (247602624631 / 250000000000) ∧
    -Real.log (247602624631 / 250000000000) ≤ (9635777 / 1000000000) := by
  have h := checkLog_sound (w := (2397375369 / 497602624631)) (n := 12)
    (lo := (150559 / 15625000)) (hi := (9635777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247602624631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247602624631) = 1/(247602624631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6237 : Bounds (-9635777 / 1000000000) (-150559 / 15625000) (Real.log (247602624631 / 250000000000)) := by
  have h := reflection_log_6237_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6238_neg : (196481667 / 1000000000) ≤ -Real.log (500000000000 / 608556504233) ∧
    -Real.log (500000000000 / 608556504233) ≤ (49120417 / 250000000) := by
  have h := checkLog_sound (w := (108556504233 / 1108556504233)) (n := 12)
    (lo := (196481667 / 1000000000)) (hi := (49120417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608556504233 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608556504233 / 500000000000) = 1/(500000000000 / 608556504233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6238 : Bounds (196481667 / 1000000000) (49120417 / 250000000) (Real.log (608556504233 / 500000000000)) := by
  have h := reflection_log_6238_neg
  have he : Real.log (608556504233 / 500000000000) = -Real.log (500000000000 / 608556504233) := by
    rw [show ((608556504233 / 500000000000) : ℝ) = ((500000000000 / 608556504233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6239_neg : (24622053 / 125000000) ≤ -Real.log (250000000000 / 304428832961) ∧
    -Real.log (250000000000 / 304428832961) ≤ (7879057 / 40000000) := by
  have h := checkLog_sound (w := (54428832961 / 554428832961)) (n := 12)
    (lo := (24622053 / 125000000)) (hi := (7879057 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304428832961 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304428832961 / 250000000000) = 1/(250000000000 / 304428832961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6239 : Bounds (24622053 / 125000000) (7879057 / 40000000) (Real.log (304428832961 / 250000000000)) := by
  have h := reflection_log_6239_neg
  have he : Real.log (304428832961 / 250000000000) = -Real.log (250000000000 / 304428832961) := by
    rw [show ((304428832961 / 250000000000) : ℝ) = ((250000000000 / 304428832961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6240_neg : (98608877 / 250000000) ≤ -Real.log (125000000000 / 185443313051) ∧
    -Real.log (125000000000 / 185443313051) ≤ (394435509 / 1000000000) := by
  have h := checkLog_sound (w := (60443313051 / 310443313051)) (n := 12)
    (lo := (98608877 / 250000000)) (hi := (394435509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185443313051 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185443313051 / 125000000000) = 1/(125000000000 / 185443313051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6240 : Bounds (98608877 / 250000000) (394435509 / 1000000000) (Real.log (185443313051 / 125000000000)) := by
  have h := reflection_log_6240_neg
  have he : Real.log (185443313051 / 125000000000) = -Real.log (125000000000 / 185443313051) := by
    rw [show ((185443313051 / 125000000000) : ℝ) = ((125000000000 / 185443313051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6241_neg : (6166303 / 15625000) ≤ -Real.log (125000000000 / 185481867859) ∧
    -Real.log (125000000000 / 185481867859) ≤ (394643393 / 1000000000) := by
  have h := checkLog_sound (w := (60481867859 / 310481867859)) (n := 12)
    (lo := (6166303 / 15625000)) (hi := (394643393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185481867859 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185481867859 / 125000000000) = 1/(125000000000 / 185481867859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6241 : Bounds (6166303 / 15625000) (394643393 / 1000000000) (Real.log (185481867859 / 125000000000)) := by
  have h := reflection_log_6241_neg
  have he : Real.log (185481867859 / 125000000000) = -Real.log (125000000000 / 185481867859) := by
    rw [show ((185481867859 / 125000000000) : ℝ) = ((125000000000 / 185481867859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6242_neg : (178062499 / 1000000000) ≤ -Real.log (10000 / 11949) ∧
    -Real.log (10000 / 11949) ≤ (2849 / 16000) := by
  have h := checkLog_sound (w := (1949 / 21949)) (n := 12)
    (lo := (178062499 / 1000000000)) (hi := (2849 / 16000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11949 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11949 / 10000) = 1/(10000 / 11949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6242 : Bounds (178062499 / 1000000000) (2849 / 16000) (Real.log (11949 / 10000)) := by
  have h := reflection_log_6242_neg
  have he : Real.log (11949 / 10000) = -Real.log (10000 / 11949) := by
    rw [show ((11949 / 10000) : ℝ) = ((10000 / 11949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6243_neg : (43357757 / 200000000) ≤ -Real.log (8051 / 10000) ∧
    -Real.log (8051 / 10000) ≤ (108394393 / 500000000) := by
  have h := checkLog_sound (w := (1949 / 18051)) (n := 12)
    (lo := (43357757 / 200000000)) (hi := (108394393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8051) = 1/(8051 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6243 : Bounds (-108394393 / 500000000) (-43357757 / 200000000) (Real.log (8051 / 10000)) := by
  have h := reflection_log_6243_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6244_neg : (194881 / 1000000000) ≤ -Real.log (10000000 / 10001949) ∧
    -Real.log (10000000 / 10001949) ≤ (97441 / 500000000) := by
  have h := checkLog_sound (w := (1949 / 20001949)) (n := 12)
    (lo := (194881 / 1000000000)) (hi := (97441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001949 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001949 / 10000000) = 1/(10000000 / 10001949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6244 : Bounds (194881 / 1000000000) (97441 / 500000000) (Real.log (10001949 / 10000000)) := by
  have h := reflection_log_6244_neg
  have he : Real.log (10001949 / 10000000) = -Real.log (10000000 / 10001949) := by
    rw [show ((10001949 / 10000000) : ℝ) = ((10000000 / 10001949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6245_neg : (97459 / 500000000) ≤ -Real.log (9998051 / 10000000) ∧
    -Real.log (9998051 / 10000000) ≤ (194919 / 1000000000) := by
  have h := checkLog_sound (w := (1949 / 19998051)) (n := 12)
    (lo := (97459 / 500000000)) (hi := (194919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998051) = 1/(9998051 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6245 : Bounds (-194919 / 1000000000) (-97459 / 500000000) (Real.log (9998051 / 10000000)) := by
  have h := reflection_log_6245_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6246_neg : (18693879 / 200000000) ≤ -Real.log (1000000 / 1097977) ∧
    -Real.log (1000000 / 1097977) ≤ (23367349 / 250000000) := by
  have h := checkLog_sound (w := (97977 / 2097977)) (n := 12)
    (lo := (18693879 / 200000000)) (hi := (23367349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097977 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097977 / 1000000) = 1/(1000000 / 1097977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6246 : Bounds (18693879 / 200000000) (23367349 / 250000000) (Real.log (1097977 / 1000000)) := by
  have h := reflection_log_6246_neg
  have he : Real.log (1097977 / 1000000) = -Real.log (1000000 / 1097977) := by
    rw [show ((1097977 / 1000000) : ℝ) = ((1000000 / 1097977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6247_neg : (5155763 / 50000000) ≤ -Real.log (902023 / 1000000) ∧
    -Real.log (902023 / 1000000) ≤ (103115261 / 1000000000) := by
  have h := checkLog_sound (w := (97977 / 1902023)) (n := 12)
    (lo := (5155763 / 50000000)) (hi := (103115261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902023) = 1/(902023 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6247 : Bounds (-103115261 / 1000000000) (-5155763 / 50000000) (Real.log (902023 / 1000000)) := by
  have h := reflection_log_6247_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6248_neg : (23423127 / 250000000) ≤ -Real.log (500000 / 549111) ∧
    -Real.log (500000 / 549111) ≤ (93692509 / 1000000000) := by
  have h := checkLog_sound (w := (49111 / 1049111)) (n := 12)
    (lo := (23423127 / 250000000)) (hi := (93692509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549111 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549111 / 500000) = 1/(500000 / 549111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6248 : Bounds (23423127 / 250000000) (93692509 / 1000000000) (Real.log (549111 / 500000)) := by
  have h := reflection_log_6248_neg
  have he : Real.log (549111 / 500000) = -Real.log (500000 / 549111) := by
    rw [show ((549111 / 500000) : ℝ) = ((500000 / 549111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6249_neg : (25846727 / 250000000) ≤ -Real.log (450889 / 500000) ∧
    -Real.log (450889 / 500000) ≤ (103386909 / 1000000000) := by
  have h := checkLog_sound (w := (49111 / 950889)) (n := 12)
    (lo := (25846727 / 250000000)) (hi := (103386909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450889) = 1/(450889 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6249 : Bounds (-103386909 / 1000000000) (-25846727 / 250000000) (Real.log (450889 / 500000)) := by
  have h := reflection_log_6249_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6250_neg : (6059 / 625000) ≤ -Real.log (247588109679 / 250000000000) ∧
    -Real.log (247588109679 / 250000000000) ≤ (9694401 / 1000000000) := by
  have h := checkLog_sound (w := (2411890321 / 497588109679)) (n := 12)
    (lo := (6059 / 625000)) (hi := (9694401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247588109679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247588109679) = 1/(247588109679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6250 : Bounds (-9694401 / 1000000000) (-6059 / 625000) (Real.log (247588109679 / 250000000000)) := by
  have h := reflection_log_6250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6251_neg : (1205733 / 125000000) ≤ -Real.log (990400507471 / 1000000000000) ∧
    -Real.log (990400507471 / 1000000000000) ≤ (1929173 / 200000000) := by
  have h := checkLog_sound (w := (9599492529 / 1990400507471)) (n := 12)
    (lo := (1205733 / 125000000)) (hi := (1929173 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990400507471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990400507471) = 1/(990400507471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6251 : Bounds (-1929173 / 200000000) (-1205733 / 125000000) (Real.log (990400507471 / 1000000000000)) := by
  have h := reflection_log_6251_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6252_neg : (12286541 / 62500000) ≤ -Real.log (10000000000 / 12172383631) ∧
    -Real.log (10000000000 / 12172383631) ≤ (196584657 / 1000000000) := by
  have h := checkLog_sound (w := (2172383631 / 22172383631)) (n := 12)
    (lo := (12286541 / 62500000)) (hi := (196584657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12172383631 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12172383631 / 10000000000) = 1/(10000000000 / 12172383631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6252 : Bounds (12286541 / 62500000) (196584657 / 1000000000) (Real.log (12172383631 / 10000000000)) := by
  have h := reflection_log_6252_neg
  have he : Real.log (12172383631 / 10000000000) = -Real.log (10000000000 / 12172383631) := by
    rw [show ((12172383631 / 10000000000) : ℝ) = ((10000000000 / 12172383631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6253_neg : (197079417 / 1000000000) ≤ -Real.log (5000000000 / 6089203773) ∧
    -Real.log (5000000000 / 6089203773) ≤ (98539709 / 500000000) := by
  have h := checkLog_sound (w := (1089203773 / 11089203773)) (n := 12)
    (lo := (197079417 / 1000000000)) (hi := (98539709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6089203773 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6089203773 / 5000000000) = 1/(5000000000 / 6089203773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6253 : Bounds (197079417 / 1000000000) (98539709 / 500000000) (Real.log (6089203773 / 5000000000)) := by
  have h := reflection_log_6253_neg
  have he : Real.log (6089203773 / 5000000000) = -Real.log (5000000000 / 6089203773) := by
    rw [show ((6089203773 / 5000000000) : ℝ) = ((5000000000 / 6089203773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6254_neg : (6166303 / 15625000) ≤ -Real.log (100000000000 / 148385494287) ∧
    -Real.log (100000000000 / 148385494287) ≤ (394643393 / 1000000000) := by
  have h := checkLog_sound (w := (48385494287 / 248385494287)) (n := 12)
    (lo := (6166303 / 15625000)) (hi := (394643393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148385494287 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148385494287 / 100000000000) = 1/(100000000000 / 148385494287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6254 : Bounds (6166303 / 15625000) (394643393 / 1000000000) (Real.log (148385494287 / 100000000000)) := by
  have h := reflection_log_6254_neg
  have he : Real.log (148385494287 / 100000000000) = -Real.log (100000000000 / 148385494287) := by
    rw [show ((148385494287 / 100000000000) : ℝ) = ((100000000000 / 148385494287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6255_neg : (78970257 / 200000000) ≤ -Real.log (250000000000 / 371040864489) ∧
    -Real.log (250000000000 / 371040864489) ≤ (197425643 / 500000000) := by
  have h := checkLog_sound (w := (121040864489 / 621040864489)) (n := 12)
    (lo := (78970257 / 200000000)) (hi := (197425643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((371040864489 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(371040864489 / 250000000000) = 1/(250000000000 / 371040864489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6255 : Bounds (78970257 / 200000000) (197425643 / 500000000) (Real.log (371040864489 / 250000000000)) := by
  have h := reflection_log_6255_neg
  have he : Real.log (371040864489 / 250000000000) = -Real.log (250000000000 / 371040864489) := by
    rw [show ((371040864489 / 250000000000) : ℝ) = ((250000000000 / 371040864489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6256_neg : (35629237 / 200000000) ≤ -Real.log (200 / 239) ∧
    -Real.log (200 / 239) ≤ (89073093 / 500000000) := by
  have h := checkLog_sound (w := (39 / 439)) (n := 12)
    (lo := (35629237 / 200000000)) (hi := (89073093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239 / 200) = 1/(200 / 239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6256 : Bounds (35629237 / 200000000) (89073093 / 500000000) (Real.log (239 / 200)) := by
  have h := reflection_log_6256_neg
  have he : Real.log (239 / 200) = -Real.log (200 / 239) := by
    rw [show ((239 / 200) : ℝ) = ((200 / 239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6257_neg : (216913001 / 1000000000) ≤ -Real.log (161 / 200) ∧
    -Real.log (161 / 200) ≤ (108456501 / 500000000) := by
  have h := checkLog_sound (w := (39 / 361)) (n := 12)
    (lo := (216913001 / 1000000000)) (hi := (108456501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 161) = 1/(161 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6257 : Bounds (-108456501 / 500000000) (-216913001 / 1000000000) (Real.log (161 / 200)) := by
  have h := reflection_log_6257_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6258_neg : (9749 / 50000000) ≤ -Real.log (200000 / 200039) ∧
    -Real.log (200000 / 200039) ≤ (194981 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 400039)) (n := 12)
    (lo := (9749 / 50000000)) (hi := (194981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200039 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200039 / 200000) = 1/(200000 / 200039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6258 : Bounds (9749 / 50000000) (194981 / 1000000000) (Real.log (200039 / 200000)) := by
  have h := reflection_log_6258_neg
  have he : Real.log (200039 / 200000) = -Real.log (200000 / 200039) := by
    rw [show ((200039 / 200000) : ℝ) = ((200000 / 200039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6259_neg : (195019 / 1000000000) ≤ -Real.log (199961 / 200000) ∧
    -Real.log (199961 / 200000) ≤ (9751 / 50000000) := by
  have h := checkLog_sound (w := (39 / 399961)) (n := 12)
    (lo := (195019 / 1000000000)) (hi := (9751 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199961) = 1/(199961 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6259 : Bounds (-9751 / 50000000) (-195019 / 1000000000) (Real.log (199961 / 200000)) := by
  have h := reflection_log_6259_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6260_neg : (93515843 / 1000000000) ≤ -Real.log (250000 / 274507) ∧
    -Real.log (250000 / 274507) ≤ (23378961 / 250000000) := by
  have h := checkLog_sound (w := (24507 / 524507)) (n := 12)
    (lo := (93515843 / 1000000000)) (hi := (23378961 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274507 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274507 / 250000) = 1/(250000 / 274507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6260 : Bounds (93515843 / 1000000000) (23378961 / 250000000) (Real.log (274507 / 250000)) := by
  have h := reflection_log_6260_neg
  have he : Real.log (274507 / 250000) = -Real.log (250000 / 274507) := by
    rw [show ((274507 / 250000) : ℝ) = ((250000 / 274507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6261_neg : (103171801 / 1000000000) ≤ -Real.log (225493 / 250000) ∧
    -Real.log (225493 / 250000) ≤ (51585901 / 500000000) := by
  have h := checkLog_sound (w := (24507 / 475493)) (n := 12)
    (lo := (103171801 / 1000000000)) (hi := (51585901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225493) = 1/(225493 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6261 : Bounds (-51585901 / 500000000) (-103171801 / 1000000000) (Real.log (225493 / 250000)) := by
  have h := reflection_log_6261_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6262_neg : (46869473 / 500000000) ≤ -Real.log (1000000 / 1098273) ∧
    -Real.log (1000000 / 1098273) ≤ (93738947 / 1000000000) := by
  have h := checkLog_sound (w := (98273 / 2098273)) (n := 12)
    (lo := (46869473 / 500000000)) (hi := (93738947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098273 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098273 / 1000000) = 1/(1000000 / 1098273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6262 : Bounds (46869473 / 500000000) (93738947 / 1000000000) (Real.log (1098273 / 1000000)) := by
  have h := reflection_log_6262_neg
  have he : Real.log (1098273 / 1000000) = -Real.log (1000000 / 1098273) := by
    rw [show ((1098273 / 1000000) : ℝ) = ((1000000 / 1098273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6263_neg : (20688693 / 200000000) ≤ -Real.log (901727 / 1000000) ∧
    -Real.log (901727 / 1000000) ≤ (51721733 / 500000000) := by
  have h := checkLog_sound (w := (98273 / 1901727)) (n := 12)
    (lo := (20688693 / 200000000)) (hi := (51721733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901727) = 1/(901727 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6263 : Bounds (-51721733 / 500000000) (-20688693 / 200000000) (Real.log (901727 / 1000000)) := by
  have h := reflection_log_6263_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6264_neg : (9704519 / 1000000000) ≤ -Real.log (990342417471 / 1000000000000) ∧
    -Real.log (990342417471 / 1000000000000) ≤ (242613 / 25000000) := by
  have h := checkLog_sound (w := (9657582529 / 1990342417471)) (n := 12)
    (lo := (9704519 / 1000000000)) (hi := (242613 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990342417471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990342417471) = 1/(990342417471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6264 : Bounds (-242613 / 25000000) (-9704519 / 1000000000) (Real.log (990342417471 / 1000000000000)) := by
  have h := reflection_log_6264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6265_neg : (9655957 / 1000000000) ≤ -Real.log (61899406951 / 62500000000) ∧
    -Real.log (61899406951 / 62500000000) ≤ (4827979 / 500000000) := by
  have h := checkLog_sound (w := (600593049 / 124399406951)) (n := 12)
    (lo := (9655957 / 1000000000)) (hi := (4827979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61899406951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61899406951) = 1/(61899406951 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6265 : Bounds (-4827979 / 500000000) (-9655957 / 1000000000) (Real.log (61899406951 / 62500000000)) := by
  have h := reflection_log_6265_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6266_neg : (39337529 / 200000000) ≤ -Real.log (100000000000 / 121736373191) ∧
    -Real.log (100000000000 / 121736373191) ≤ (98343823 / 500000000) := by
  have h := checkLog_sound (w := (21736373191 / 221736373191)) (n := 12)
    (lo := (39337529 / 200000000)) (hi := (98343823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121736373191 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121736373191 / 100000000000) = 1/(100000000000 / 121736373191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6266 : Bounds (39337529 / 200000000) (98343823 / 500000000) (Real.log (121736373191 / 100000000000)) := by
  have h := reflection_log_6266_neg
  have he : Real.log (121736373191 / 100000000000) = -Real.log (100000000000 / 121736373191) := by
    rw [show ((121736373191 / 100000000000) : ℝ) = ((100000000000 / 121736373191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6267_neg : (197182411 / 1000000000) ≤ -Real.log (500000000000 / 608983095771) ∧
    -Real.log (500000000000 / 608983095771) ≤ (49295603 / 250000000) := by
  have h := checkLog_sound (w := (108983095771 / 1108983095771)) (n := 12)
    (lo := (197182411 / 1000000000)) (hi := (49295603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608983095771 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608983095771 / 500000000000) = 1/(500000000000 / 608983095771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6267 : Bounds (197182411 / 1000000000) (49295603 / 250000000) (Real.log (608983095771 / 500000000000)) := by
  have h := reflection_log_6267_neg
  have he : Real.log (608983095771 / 500000000000) = -Real.log (500000000000 / 608983095771) := by
    rw [show ((608983095771 / 500000000000) : ℝ) = ((500000000000 / 608983095771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6268_neg : (78970257 / 200000000) ≤ -Real.log (500000000000 / 742081728977) ∧
    -Real.log (500000000000 / 742081728977) ≤ (197425643 / 500000000) := by
  have h := checkLog_sound (w := (242081728977 / 1242081728977)) (n := 12)
    (lo := (78970257 / 200000000)) (hi := (197425643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742081728977 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742081728977 / 500000000000) = 1/(500000000000 / 742081728977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6268 : Bounds (78970257 / 200000000) (197425643 / 500000000) (Real.log (742081728977 / 500000000000)) := by
  have h := reflection_log_6268_neg
  have he : Real.log (742081728977 / 500000000000) = -Real.log (500000000000 / 742081728977) := by
    rw [show ((742081728977 / 500000000000) : ℝ) = ((500000000000 / 742081728977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6269_neg : (197529593 / 500000000) ≤ -Real.log (100000000000 / 148447204969) ∧
    -Real.log (100000000000 / 148447204969) ≤ (395059187 / 1000000000) := by
  have h := checkLog_sound (w := (48447204969 / 248447204969)) (n := 12)
    (lo := (197529593 / 500000000)) (hi := (395059187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148447204969 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148447204969 / 100000000000) = 1/(100000000000 / 148447204969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6269 : Bounds (197529593 / 500000000) (395059187 / 1000000000) (Real.log (148447204969 / 100000000000)) := by
  have h := reflection_log_6269_neg
  have he : Real.log (148447204969 / 100000000000) = -Real.log (100000000000 / 148447204969) := by
    rw [show ((148447204969 / 100000000000) : ℝ) = ((100000000000 / 148447204969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6270_neg : (178229863 / 1000000000) ≤ -Real.log (10000 / 11951) ∧
    -Real.log (10000 / 11951) ≤ (22278733 / 125000000) := by
  have h := checkLog_sound (w := (1951 / 21951)) (n := 12)
    (lo := (178229863 / 1000000000)) (hi := (22278733 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11951 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11951 / 10000) = 1/(10000 / 11951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6270 : Bounds (178229863 / 1000000000) (22278733 / 125000000) (Real.log (11951 / 10000)) := by
  have h := reflection_log_6270_neg
  have he : Real.log (11951 / 10000) = -Real.log (10000 / 11951) := by
    rw [show ((11951 / 10000) : ℝ) = ((10000 / 11951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6271_neg : (13564827 / 62500000) ≤ -Real.log (8049 / 10000) ∧
    -Real.log (8049 / 10000) ≤ (217037233 / 1000000000) := by
  have h := checkLog_sound (w := (1951 / 18049)) (n := 12)
    (lo := (13564827 / 62500000)) (hi := (217037233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8049) = 1/(8049 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6271 : Bounds (-217037233 / 1000000000) (-13564827 / 62500000) (Real.log (8049 / 10000)) := by
  have h := reflection_log_6271_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
