import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0153
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

theorem reflection_log_1_neg : (651103737 / 1000000000) ≤ -Real.log (6400 / 12273) ∧
    -Real.log (6400 / 12273) ≤ (325551869 / 500000000) := by
  have h := checkLog_sound (w := (5873 / 18673)) (n := 12)
    (lo := (651103737 / 1000000000)) (hi := (325551869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12273 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12273 / 6400) = 1/(6400 / 12273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (651103737 / 1000000000) (325551869 / 500000000) (Real.log (12273 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12273 / 6400) = -Real.log (6400 / 12273) := by
    rw [show ((12273 / 6400) : ℝ) = ((6400 / 12273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2496852719 / 1000000000) ≤ -Real.log (527 / 6400) ∧
    -Real.log (527 / 6400) ≤ (2496852723 / 1000000000) := by
  have h := checkLog_sound (w := (273 / 1327)) (n := 12)
    (lo := (417411179 / 1000000000)) (hi := (20870559 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 527) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 527) = 1/(527 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2496852723 / 1000000000) (-2496852719 / 1000000000) (Real.log (527 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (32516469 / 50000000) ≤ -Real.log (12800 / 24527) ∧
    -Real.log (12800 / 24527) ≤ (650329381 / 1000000000) := by
  have h := checkLog_sound (w := (11727 / 37327)) (n := 12)
    (lo := (32516469 / 50000000)) (hi := (650329381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24527 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24527 / 12800) = 1/(12800 / 24527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (32516469 / 50000000) (650329381 / 1000000000) (Real.log (24527 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24527 / 12800) = -Real.log (12800 / 24527) := by
    rw [show ((24527 / 12800) : ℝ) = ((12800 / 24527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (495797341 / 200000000) ≤ -Real.log (1073 / 12800) ∧
    -Real.log (1073 / 12800) ≤ (2478986709 / 1000000000) := by
  have h := checkLog_sound (w := (527 / 2673)) (n := 12)
    (lo := (79909033 / 200000000)) (hi := (199772583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1073) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1073) = 1/(1073 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2478986709 / 1000000000) (-495797341 / 200000000) (Real.log (1073 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (303607383 / 500000000) ≤ -Real.log (3200 / 5873) ∧
    -Real.log (3200 / 5873) ≤ (607214767 / 1000000000) := by
  have h := checkLog_sound (w := (2673 / 9073)) (n := 12)
    (lo := (303607383 / 500000000)) (hi := (607214767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5873 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5873 / 3200) = 1/(3200 / 5873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (303607383 / 500000000) (607214767 / 1000000000) (Real.log (5873 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5873 / 3200) = -Real.log (3200 / 5873) := by
    rw [show ((5873 / 3200) : ℝ) = ((3200 / 5873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1803705539 / 1000000000) ≤ -Real.log (527 / 3200) ∧
    -Real.log (527 / 3200) ≤ (901852771 / 500000000) := by
  have h := checkLog_sound (w := (273 / 1327)) (n := 12)
    (lo := (417411179 / 1000000000)) (hi := (20870559 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 527) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 527) = 1/(527 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-901852771 / 500000000) (-1803705539 / 1000000000) (Real.log (527 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (121119177 / 200000000) ≤ -Real.log (6400 / 11727) ∧
    -Real.log (6400 / 11727) ≤ (302797943 / 500000000) := by
  have h := checkLog_sound (w := (5327 / 18127)) (n := 12)
    (lo := (121119177 / 200000000)) (hi := (302797943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11727 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11727 / 6400) = 1/(6400 / 11727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (121119177 / 200000000) (302797943 / 500000000) (Real.log (11727 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11727 / 6400) = -Real.log (6400 / 11727) := by
    rw [show ((11727 / 6400) : ℝ) = ((6400 / 11727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (71433581 / 40000000) ≤ -Real.log (1073 / 6400) ∧
    -Real.log (1073 / 6400) ≤ (223229941 / 125000000) := by
  have h := checkLog_sound (w := (527 / 2673)) (n := 12)
    (lo := (79909033 / 200000000)) (hi := (199772583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1073) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1073) = 1/(1073 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-223229941 / 125000000) (-71433581 / 40000000) (Real.log (1073 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (164974759 / 250000000) ≤ -Real.log (1000000 / 1934597) ∧
    -Real.log (1000000 / 1934597) ≤ (659899037 / 1000000000) := by
  have h := checkLog_sound (w := (934597 / 2934597)) (n := 12)
    (lo := (164974759 / 250000000)) (hi := (659899037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1934597 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1934597 / 1000000) = 1/(1000000 / 1934597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (164974759 / 250000000) (659899037 / 1000000000) (Real.log (1934597 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1934597 / 1000000) = -Real.log (1000000 / 1934597) := by
    rw [show ((1934597 / 1000000) : ℝ) = ((1000000 / 1934597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (681796787 / 250000000) ≤ -Real.log (65403 / 1000000) ∧
    -Real.log (65403 / 1000000) ≤ (170449197 / 62500000) := by
  have h := checkLog_sound (w := (59597 / 190403)) (n := 12)
    (lo := (80968201 / 125000000)) (hi := (647745609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 65403) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 65403) = 1/(65403 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-170449197 / 62500000) (-681796787 / 250000000) (Real.log (65403 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (330221077 / 500000000) ≤ -Real.log (31250 / 60489) ∧
    -Real.log (31250 / 60489) ≤ (132088431 / 200000000) := by
  have h := checkLog_sound (w := (29239 / 91739)) (n := 12)
    (lo := (330221077 / 500000000)) (hi := (132088431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60489 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60489 / 31250) = 1/(31250 / 60489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (330221077 / 500000000) (132088431 / 200000000) (Real.log (60489 / 31250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60489 / 31250) = -Real.log (31250 / 60489) := by
    rw [show ((60489 / 31250) : ℝ) = ((31250 / 60489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2743387263 / 1000000000) ≤ -Real.log (2011 / 31250) ∧
    -Real.log (2011 / 31250) ≤ (2743387267 / 1000000000) := by
  have h := checkLog_sound (w := (7581 / 23669)) (n := 12)
    (lo := (663945723 / 1000000000)) (hi := (165986431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8044) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 8044) = 1/(2011 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2743387267 / 1000000000) (-2743387263 / 1000000000) (Real.log (2011 / 31250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (10298237 / 15625000) ≤ -Real.log (1000000 / 1933027) ∧
    -Real.log (1000000 / 1933027) ≤ (659087169 / 1000000000) := by
  have h := checkLog_sound (w := (933027 / 2933027)) (n := 12)
    (lo := (10298237 / 15625000)) (hi := (659087169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1933027 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1933027 / 1000000) = 1/(1000000 / 1933027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (10298237 / 15625000) (659087169 / 1000000000) (Real.log (1933027 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1933027 / 1000000) = -Real.log (1000000 / 1933027) := by
    rw [show ((1933027 / 1000000) : ℝ) = ((1000000 / 1933027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (675866431 / 250000000) ≤ -Real.log (66973 / 1000000) ∧
    -Real.log (66973 / 1000000) ≤ (10560413 / 3906250) := by
  have h := checkLog_sound (w := (58027 / 191973)) (n := 12)
    (lo := (78003023 / 125000000)) (hi := (124804837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 66973) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 66973) = 1/(66973 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10560413 / 3906250) (-675866431 / 250000000) (Real.log (66973 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (6596633 / 10000000) ≤ -Real.log (1000000 / 1934141) ∧
    -Real.log (1000000 / 1934141) ≤ (659663301 / 1000000000) := by
  have h := checkLog_sound (w := (934141 / 2934141)) (n := 12)
    (lo := (6596633 / 10000000)) (hi := (659663301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1934141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1934141 / 1000000) = 1/(1000000 / 1934141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (6596633 / 10000000) (659663301 / 1000000000) (Real.log (1934141 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1934141 / 1000000) = -Real.log (1000000 / 1934141) := by
    rw [show ((1934141 / 1000000) : ℝ) = ((1000000 / 1934141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (170014949 / 62500000) ≤ -Real.log (65859 / 1000000) ∧
    -Real.log (65859 / 1000000) ≤ (680059797 / 250000000) := by
  have h := checkLog_sound (w := (59141 / 190859)) (n := 12)
    (lo := (160199411 / 250000000)) (hi := (128159529 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 65859) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 65859) = 1/(65859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-680059797 / 250000000) (-170014949 / 62500000) (Real.log (65859 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3387086183 / 1000000000) ≤ -Real.log (250000000000 / 7394909254927) ∧
    -Real.log (250000000000 / 7394909254927) ≤ (846771547 / 250000000) := by
  have h := checkLog_sound (w := (3394909254927 / 11394909254927)) (n := 12)
    (lo := (614497463 / 1000000000)) (hi := (76812183 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7394909254927 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7394909254927 / 4000000000000) = 1/(250000000000 / 7394909254927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3387086183 / 1000000000) (846771547 / 250000000) (Real.log (7394909254927 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7394909254927 / 250000000000) = -Real.log (250000000000 / 7394909254927) := by
    rw [show ((7394909254927 / 250000000000) : ℝ) = ((250000000000 / 7394909254927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3403829417 / 1000000000) ≤ -Real.log (500000000000 / 15039532570861) ∧
    -Real.log (500000000000 / 15039532570861) ≤ (1701914711 / 500000000) := by
  have h := checkLog_sound (w := (7039532570861 / 23039532570861)) (n := 12)
    (lo := (631240697 / 1000000000)) (hi := (315620349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15039532570861 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15039532570861 / 8000000000000) = 1/(500000000000 / 15039532570861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3403829417 / 1000000000) (1701914711 / 500000000) (Real.log (15039532570861 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (15039532570861 / 500000000000) = -Real.log (500000000000 / 15039532570861) := by
    rw [show ((15039532570861 / 500000000000) : ℝ) = ((500000000000 / 15039532570861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3362552891 / 1000000000) ≤ -Real.log (500000000000 / 14431390261747) ∧
    -Real.log (500000000000 / 14431390261747) ≤ (52539889 / 15625000) := by
  have h := checkLog_sound (w := (6431390261747 / 22431390261747)) (n := 12)
    (lo := (589964171 / 1000000000)) (hi := (147491043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14431390261747 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(14431390261747 / 8000000000000) = 1/(500000000000 / 14431390261747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3362552891 / 1000000000) (52539889 / 15625000) (Real.log (14431390261747 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (14431390261747 / 500000000000) = -Real.log (500000000000 / 14431390261747) := by
    rw [show ((14431390261747 / 500000000000) : ℝ) = ((500000000000 / 14431390261747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3379902483 / 1000000000) ≤ -Real.log (250000000000 / 7341976798919) ∧
    -Real.log (250000000000 / 7341976798919) ≤ (422487811 / 125000000) := by
  have h := checkLog_sound (w := (3341976798919 / 11341976798919)) (n := 12)
    (lo := (607313763 / 1000000000)) (hi := (151828441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7341976798919 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7341976798919 / 4000000000000) = 1/(250000000000 / 7341976798919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3379902483 / 1000000000) (422487811 / 125000000) (Real.log (7341976798919 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7341976798919 / 250000000000) = -Real.log (250000000000 / 7341976798919) := by
    rw [show ((7341976798919 / 250000000000) : ℝ) = ((250000000000 / 7341976798919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0153
