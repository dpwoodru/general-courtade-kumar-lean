import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0257
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

theorem reflection_log_1_neg : (239724081 / 1000000000) ≤ -Real.log (5120 / 6507) ∧
    -Real.log (5120 / 6507) ≤ (119862041 / 500000000) := by
  have h := checkLog_sound (w := (1387 / 11627)) (n := 12)
    (lo := (239724081 / 1000000000)) (hi := (119862041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6507 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6507 / 5120) = 1/(5120 / 6507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (239724081 / 1000000000) (119862041 / 500000000) (Real.log (6507 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6507 / 5120) = -Real.log (5120 / 6507) := by
    rw [show ((6507 / 5120) : ℝ) = ((5120 / 6507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (315942239 / 1000000000) ≤ -Real.log (3733 / 5120) ∧
    -Real.log (3733 / 5120) ≤ (1974639 / 6250000) := by
  have h := checkLog_sound (w := (1387 / 8853)) (n := 12)
    (lo := (315942239 / 1000000000)) (hi := (1974639 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3733) = 1/(3733 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1974639 / 6250000) (-315942239 / 1000000000) (Real.log (3733 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (239262933 / 1000000000) ≤ -Real.log (640 / 813) ∧
    -Real.log (640 / 813) ≤ (119631467 / 500000000) := by
  have h := checkLog_sound (w := (173 / 1453)) (n := 12)
    (lo := (239262933 / 1000000000)) (hi := (119631467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813 / 640) = 1/(640 / 813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (239262933 / 1000000000) (119631467 / 500000000) (Real.log (813 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (813 / 640) = -Real.log (640 / 813) := by
    rw [show ((813 / 640) : ℝ) = ((640 / 813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (157569459 / 500000000) ≤ -Real.log (467 / 640) ∧
    -Real.log (467 / 640) ≤ (315138919 / 1000000000) := by
  have h := checkLog_sound (w := (173 / 1107)) (n := 12)
    (lo := (157569459 / 500000000)) (hi := (315138919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 467) = 1/(467 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-315138919 / 1000000000) (-157569459 / 500000000) (Real.log (467 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (216474269 / 500000000) ≤ -Real.log (2560 / 3947) ∧
    -Real.log (2560 / 3947) ≤ (432948539 / 1000000000) := by
  have h := checkLog_sound (w := (1387 / 6507)) (n := 12)
    (lo := (216474269 / 500000000)) (hi := (432948539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3947 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3947 / 2560) = 1/(2560 / 3947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (216474269 / 500000000) (432948539 / 1000000000) (Real.log (3947 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3947 / 2560) = -Real.log (2560 / 3947) := by
    rw [show ((3947 / 2560) : ℝ) = ((2560 / 3947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (12194417 / 15625000) ≤ -Real.log (1173 / 2560) ∧
    -Real.log (1173 / 2560) ≤ (78044269 / 100000000) := by
  have h := checkLog_sound (w := (107 / 2453)) (n := 12)
    (lo := (21823877 / 250000000)) (hi := (87295509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1173) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1173) = 1/(1173 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-78044269 / 100000000) (-12194417 / 15625000) (Real.log (1173 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (216094089 / 500000000) ≤ -Real.log (320 / 493) ∧
    -Real.log (320 / 493) ≤ (432188179 / 1000000000) := by
  have h := checkLog_sound (w := (173 / 813)) (n := 12)
    (lo := (216094089 / 500000000)) (hi := (432188179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493 / 320) = 1/(320 / 493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (216094089 / 500000000) (432188179 / 1000000000) (Real.log (493 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (493 / 320) = -Real.log (320 / 493) := by
    rw [show ((493 / 320) : ℝ) = ((320 / 493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (97236051 / 125000000) ≤ -Real.log (147 / 320) ∧
    -Real.log (147 / 320) ≤ (77788841 / 100000000) := by
  have h := checkLog_sound (w := (13 / 307)) (n := 12)
    (lo := (21185307 / 250000000)) (hi := (84741229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 147) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 147) = 1/(147 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-77788841 / 100000000) (-97236051 / 125000000) (Real.log (147 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (327581401 / 1000000000) ≤ -Real.log (125000 / 173451) ∧
    -Real.log (125000 / 173451) ≤ (163790701 / 500000000) := by
  have h := checkLog_sound (w := (48451 / 298451)) (n := 12)
    (lo := (327581401 / 1000000000)) (hi := (163790701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173451 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173451 / 125000) = 1/(125000 / 173451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (327581401 / 1000000000) (163790701 / 500000000) (Real.log (173451 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (173451 / 125000) = -Real.log (125000 / 173451) := by
    rw [show ((173451 / 125000) : ℝ) = ((125000 / 173451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (245191339 / 500000000) ≤ -Real.log (76549 / 125000) ∧
    -Real.log (76549 / 125000) ≤ (490382679 / 1000000000) := by
  have h := checkLog_sound (w := (48451 / 201549)) (n := 12)
    (lo := (245191339 / 500000000)) (hi := (490382679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 76549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 76549) = 1/(76549 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-490382679 / 1000000000) (-245191339 / 500000000) (Real.log (76549 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (164103371 / 500000000) ≤ -Real.log (250000 / 347119) ∧
    -Real.log (250000 / 347119) ≤ (328206743 / 1000000000) := by
  have h := checkLog_sound (w := (97119 / 597119)) (n := 12)
    (lo := (164103371 / 500000000)) (hi := (328206743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347119 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347119 / 250000) = 1/(250000 / 347119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (164103371 / 500000000) (328206743 / 1000000000) (Real.log (347119 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (347119 / 250000) = -Real.log (250000 / 347119) := by
    rw [show ((347119 / 250000) : ℝ) = ((250000 / 347119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (122950269 / 250000000) ≤ -Real.log (152881 / 250000) ∧
    -Real.log (152881 / 250000) ≤ (491801077 / 1000000000) := by
  have h := checkLog_sound (w := (97119 / 402881)) (n := 12)
    (lo := (122950269 / 250000000)) (hi := (491801077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 152881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 152881) = 1/(152881 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-491801077 / 1000000000) (-122950269 / 250000000) (Real.log (152881 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (251505521 / 1000000000) ≤ -Real.log (25000 / 32149) ∧
    -Real.log (25000 / 32149) ≤ (125752761 / 500000000) := by
  have h := checkLog_sound (w := (7149 / 57149)) (n := 12)
    (lo := (251505521 / 1000000000)) (hi := (125752761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32149 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32149 / 25000) = 1/(25000 / 32149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (251505521 / 1000000000) (125752761 / 500000000) (Real.log (32149 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (32149 / 25000) = -Real.log (25000 / 32149) := by
    rw [show ((32149 / 25000) : ℝ) = ((25000 / 32149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (67363259 / 200000000) ≤ -Real.log (17851 / 25000) ∧
    -Real.log (17851 / 25000) ≤ (42102037 / 125000000) := by
  have h := checkLog_sound (w := (7149 / 42851)) (n := 12)
    (lo := (67363259 / 200000000)) (hi := (42102037 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 17851) = 1/(17851 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-42102037 / 125000000) (-67363259 / 200000000) (Real.log (17851 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (63011651 / 250000000) ≤ -Real.log (15625 / 20104) ∧
    -Real.log (15625 / 20104) ≤ (50409321 / 200000000) := by
  have h := checkLog_sound (w := (4479 / 35729)) (n := 12)
    (lo := (63011651 / 250000000)) (hi := (50409321 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20104 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20104 / 15625) = 1/(15625 / 20104) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (63011651 / 250000000) (50409321 / 200000000) (Real.log (20104 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (20104 / 15625) = -Real.log (15625 / 20104) := by
    rw [show ((20104 / 15625) : ℝ) = ((15625 / 20104) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (168895753 / 500000000) ≤ -Real.log (11146 / 15625) ∧
    -Real.log (11146 / 15625) ≤ (337791507 / 1000000000) := by
  have h := checkLog_sound (w := (4479 / 26771)) (n := 12)
    (lo := (168895753 / 500000000)) (hi := (337791507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11146) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11146) = 1/(11146 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-337791507 / 1000000000) (-168895753 / 500000000) (Real.log (11146 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (817964079 / 1000000000) ≤ -Real.log (125000000000 / 283235248011) ∧
    -Real.log (125000000000 / 283235248011) ≤ (817964081 / 1000000000) := by
  have h := checkLog_sound (w := (33235248011 / 533235248011)) (n := 12)
    (lo := (124816899 / 1000000000)) (hi := (1248169 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((283235248011 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(283235248011 / 250000000000) = 1/(125000000000 / 283235248011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (817964079 / 1000000000) (817964081 / 1000000000) (Real.log (283235248011 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (283235248011 / 125000000000) = -Real.log (125000000000 / 283235248011) := by
    rw [show ((283235248011 / 125000000000) : ℝ) = ((125000000000 / 283235248011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (820007819 / 1000000000) ≤ -Real.log (250000000000 / 567629398029) ∧
    -Real.log (250000000000 / 567629398029) ≤ (820007821 / 1000000000) := by
  have h := checkLog_sound (w := (67629398029 / 1067629398029)) (n := 12)
    (lo := (126860639 / 1000000000)) (hi := (792879 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567629398029 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(567629398029 / 500000000000) = 1/(250000000000 / 567629398029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (820007819 / 1000000000) (820007821 / 1000000000) (Real.log (567629398029 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (567629398029 / 250000000000) = -Real.log (250000000000 / 567629398029) := by
    rw [show ((567629398029 / 250000000000) : ℝ) = ((250000000000 / 567629398029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (73540227 / 125000000) ≤ -Real.log (500000000000 / 900481765727) ∧
    -Real.log (500000000000 / 900481765727) ≤ (588321817 / 1000000000) := by
  have h := checkLog_sound (w := (400481765727 / 1400481765727)) (n := 12)
    (lo := (73540227 / 125000000)) (hi := (588321817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((900481765727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(900481765727 / 500000000000) = 1/(500000000000 / 900481765727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (73540227 / 125000000) (588321817 / 1000000000) (Real.log (900481765727 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (900481765727 / 500000000000) = -Real.log (500000000000 / 900481765727) := by
    rw [show ((900481765727 / 500000000000) : ℝ) = ((500000000000 / 900481765727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (589838111 / 1000000000) ≤ -Real.log (500000000000 / 901848196663) ∧
    -Real.log (500000000000 / 901848196663) ≤ (18432441 / 31250000) := by
  have h := checkLog_sound (w := (401848196663 / 1401848196663)) (n := 12)
    (lo := (589838111 / 1000000000)) (hi := (18432441 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((901848196663 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(901848196663 / 500000000000) = 1/(500000000000 / 901848196663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (589838111 / 1000000000) (18432441 / 31250000) (Real.log (901848196663 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (901848196663 / 500000000000) = -Real.log (500000000000 / 901848196663) := by
    rw [show ((901848196663 / 500000000000) : ℝ) = ((500000000000 / 901848196663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0257
