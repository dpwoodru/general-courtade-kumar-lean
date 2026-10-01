import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0023
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

theorem reflection_log_1_neg : (13631927 / 20000000) ≤ -Real.log (6400 / 12653) ∧
    -Real.log (6400 / 12653) ≤ (681596351 / 1000000000) := by
  have h := checkLog_sound (w := (6253 / 19053)) (n := 12)
    (lo := (13631927 / 20000000)) (hi := (681596351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12653 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12653 / 6400) = 1/(6400 / 12653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13631927 / 20000000) (681596351 / 1000000000) (Real.log (12653 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12653 / 6400) = -Real.log (6400 / 12653) := by
    rw [show ((12653 / 6400) : ℝ) = ((6400 / 12653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3773620679 / 1000000000) ≤ -Real.log (147 / 6400) ∧
    -Real.log (147 / 6400) ≤ (754724137 / 200000000) := by
  have h := checkLog_sound (w := (53 / 347)) (n := 12)
    (lo := (307884779 / 1000000000)) (hi := (15394239 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 147) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(200 / 147) = 1/(147 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-754724137 / 200000000) (-3773620679 / 1000000000) (Real.log (147 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (136300499 / 200000000) ≤ -Real.log (102400 / 202429) ∧
    -Real.log (102400 / 202429) ≤ (21296953 / 31250000) := by
  have h := checkLog_sound (w := (100029 / 304829)) (n := 12)
    (lo := (136300499 / 200000000)) (hi := (21296953 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202429 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202429 / 102400) = 1/(102400 / 202429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (136300499 / 200000000) (21296953 / 31250000) (Real.log (202429 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202429 / 102400) = -Real.log (102400 / 202429) := by
    rw [show ((202429 / 102400) : ℝ) = ((102400 / 202429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1882787451 / 500000000) ≤ -Real.log (2371 / 102400) ∧
    -Real.log (2371 / 102400) ≤ (941393727 / 250000000) := by
  have h := checkLog_sound (w := (829 / 5571)) (n := 12)
    (lo := (149919501 / 500000000)) (hi := (299839003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2371) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2371) = 1/(2371 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-941393727 / 250000000) (-1882787451 / 500000000) (Real.log (2371 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (334955269 / 500000000) ≤ -Real.log (3200 / 6253) ∧
    -Real.log (3200 / 6253) ≤ (669910539 / 1000000000) := by
  have h := checkLog_sound (w := (3053 / 9453)) (n := 12)
    (lo := (334955269 / 500000000)) (hi := (669910539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6253 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6253 / 3200) = 1/(3200 / 6253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (334955269 / 500000000) (669910539 / 1000000000) (Real.log (6253 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (6253 / 3200) = -Real.log (3200 / 6253) := by
    rw [show ((6253 / 3200) : ℝ) = ((3200 / 6253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3080473499 / 1000000000) ≤ -Real.log (147 / 3200) ∧
    -Real.log (147 / 3200) ≤ (96264797 / 31250000) := by
  have h := checkLog_sound (w := (53 / 347)) (n := 12)
    (lo := (307884779 / 1000000000)) (hi := (15394239 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 147) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 147) = 1/(147 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-96264797 / 31250000) (-3080473499 / 1000000000) (Real.log (147 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (669720611 / 1000000000) ≤ -Real.log (51200 / 100029) ∧
    -Real.log (51200 / 100029) ≤ (167430153 / 250000000) := by
  have h := checkLog_sound (w := (48829 / 151229)) (n := 12)
    (lo := (669720611 / 1000000000)) (hi := (167430153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100029 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100029 / 51200) = 1/(51200 / 100029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (669720611 / 1000000000) (167430153 / 250000000) (Real.log (100029 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (100029 / 51200) = -Real.log (51200 / 100029) := by
    rw [show ((100029 / 51200) : ℝ) = ((51200 / 100029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1536213861 / 500000000) ≤ -Real.log (2371 / 51200) ∧
    -Real.log (2371 / 51200) ≤ (3072427727 / 1000000000) := by
  have h := checkLog_sound (w := (829 / 5571)) (n := 12)
    (lo := (149919501 / 500000000)) (hi := (299839003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2371) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2371) = 1/(2371 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3072427727 / 1000000000) (-1536213861 / 500000000) (Real.log (2371 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (683307933 / 1000000000) ≤ -Real.log (500000 / 990209) ∧
    -Real.log (500000 / 990209) ≤ (341653967 / 500000000) := by
  have h := checkLog_sound (w := (490209 / 1490209)) (n := 12)
    (lo := (683307933 / 1000000000)) (hi := (341653967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990209 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990209 / 500000) = 1/(500000 / 990209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (683307933 / 1000000000) (341653967 / 500000000) (Real.log (990209 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (990209 / 500000) = -Real.log (500000 / 990209) := by
    rw [show ((990209 / 500000) : ℝ) = ((500000 / 990209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3933144499 / 1000000000) ≤ -Real.log (9791 / 500000) ∧
    -Real.log (9791 / 500000) ≤ (786628901 / 200000000) := by
  have h := checkLog_sound (w := (2917 / 12708)) (n := 12)
    (lo := (467408599 / 1000000000)) (hi := (2337043 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9791) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9791) = 1/(9791 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-786628901 / 200000000) (-3933144499 / 1000000000) (Real.log (9791 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (341692341 / 500000000) ≤ -Real.log (100000 / 198057) ∧
    -Real.log (100000 / 198057) ≤ (683384683 / 1000000000) := by
  have h := checkLog_sound (w := (98057 / 298057)) (n := 12)
    (lo := (341692341 / 500000000)) (hi := (683384683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198057 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198057 / 100000) = 1/(100000 / 198057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (341692341 / 500000000) (683384683 / 1000000000) (Real.log (198057 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (198057 / 100000) = -Real.log (100000 / 198057) := by
    rw [show ((198057 / 100000) : ℝ) = ((100000 / 198057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (985234253 / 250000000) ≤ -Real.log (1943 / 100000) ∧
    -Real.log (1943 / 100000) ≤ (1970468509 / 500000000) := by
  have h := checkLog_sound (w := (591 / 2534)) (n := 12)
    (lo := (59400139 / 125000000)) (hi := (475201113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1943) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1943) = 1/(1943 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1970468509 / 500000000) (-985234253 / 250000000) (Real.log (1943 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (170816253 / 250000000) ≤ -Real.log (1000000 / 1980333) ∧
    -Real.log (1000000 / 1980333) ≤ (683265013 / 1000000000) := by
  have h := checkLog_sound (w := (980333 / 2980333)) (n := 12)
    (lo := (170816253 / 250000000)) (hi := (683265013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980333 / 1000000) = 1/(1000000 / 1980333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (170816253 / 250000000) (683265013 / 1000000000) (Real.log (1980333 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1980333 / 1000000) = -Real.log (1000000 / 1980333) := by
    rw [show ((1980333 / 1000000) : ℝ) = ((1000000 / 1980333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3928813171 / 1000000000) ≤ -Real.log (19667 / 1000000) ∧
    -Real.log (19667 / 1000000) ≤ (3928813177 / 1000000000) := by
  have h := checkLog_sound (w := (11583 / 50917)) (n := 12)
    (lo := (463077271 / 1000000000)) (hi := (57884659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19667) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19667) = 1/(19667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3928813177 / 1000000000) (-3928813171 / 1000000000) (Real.log (19667 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (683342269 / 1000000000) ≤ -Real.log (500000 / 990243) ∧
    -Real.log (500000 / 990243) ≤ (68334227 / 100000000) := by
  have h := checkLog_sound (w := (490243 / 1490243)) (n := 12)
    (lo := (683342269 / 1000000000)) (hi := (68334227 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990243 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990243 / 500000) = 1/(500000 / 990243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (683342269 / 1000000000) (68334227 / 100000000) (Real.log (990243 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (990243 / 500000) = -Real.log (500000 / 990243) := by
    rw [show ((990243 / 500000) : ℝ) = ((500000 / 990243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3936623119 / 1000000000) ≤ -Real.log (9757 / 500000) ∧
    -Real.log (9757 / 500000) ≤ (6298597 / 1600000) := by
  have h := checkLog_sound (w := (2934 / 12691)) (n := 12)
    (lo := (470887219 / 1000000000)) (hi := (23544361 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9757) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9757) = 1/(9757 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-6298597 / 1600000) (-3936623119 / 1000000000) (Real.log (9757 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (288528277 / 62500000) ≤ -Real.log (125000000000 / 12641826677561) ∧
    -Real.log (125000000000 / 12641826677561) ≤ (4616452439 / 1000000000) := by
  have h := checkLog_sound (w := (4641826677561 / 20641826677561)) (n := 12)
    (lo := (57196169 / 125000000)) (hi := (457569353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12641826677561 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(12641826677561 / 8000000000000) = 1/(125000000000 / 12641826677561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (288528277 / 62500000) (4616452439 / 1000000000) (Real.log (12641826677561 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12641826677561 / 125000000000) = -Real.log (125000000000 / 12641826677561) := by
    rw [show ((12641826677561 / 125000000000) : ℝ) = ((125000000000 / 12641826677561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2312160847 / 500000000) ≤ -Real.log (250000000000 / 25483401955739) ∧
    -Real.log (250000000000 / 25483401955739) ≤ (4624321701 / 1000000000) := by
  have h := checkLog_sound (w := (9483401955739 / 41483401955739)) (n := 12)
    (lo := (232719307 / 500000000)) (hi := (93087723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25483401955739 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(25483401955739 / 16000000000000) = 1/(250000000000 / 25483401955739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2312160847 / 500000000) (4624321701 / 1000000000) (Real.log (25483401955739 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (25483401955739 / 250000000000) = -Real.log (250000000000 / 25483401955739) := by
    rw [show ((25483401955739 / 250000000000) : ℝ) = ((250000000000 / 25483401955739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4612078183 / 1000000000) ≤ -Real.log (500000000000 / 50346595820409) ∧
    -Real.log (500000000000 / 50346595820409) ≤ (461207819 / 100000000) := by
  have h := checkLog_sound (w := (18346595820409 / 82346595820409)) (n := 12)
    (lo := (453195103 / 1000000000)) (hi := (14162347 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50346595820409 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(50346595820409 / 32000000000000) = 1/(500000000000 / 50346595820409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4612078183 / 1000000000) (461207819 / 100000000) (Real.log (50346595820409 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (50346595820409 / 500000000000) = -Real.log (500000000000 / 50346595820409) := by
    rw [show ((50346595820409 / 500000000000) : ℝ) = ((500000000000 / 50346595820409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1154991347 / 250000000) ≤ -Real.log (125000000000 / 12686314953367) ∧
    -Real.log (125000000000 / 12686314953367) ≤ (923993079 / 200000000) := by
  have h := checkLog_sound (w := (4686314953367 / 20686314953367)) (n := 12)
    (lo := (115270577 / 250000000)) (hi := (461082309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12686314953367 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(12686314953367 / 8000000000000) = 1/(125000000000 / 12686314953367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1154991347 / 250000000) (923993079 / 200000000) (Real.log (12686314953367 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (12686314953367 / 125000000000) = -Real.log (125000000000 / 12686314953367) := by
    rw [show ((12686314953367 / 125000000000) : ℝ) = ((125000000000 / 12686314953367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0023
