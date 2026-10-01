import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0199
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

theorem reflection_log_1_neg : (23815861 / 40000000) ≤ -Real.log (800 / 1451) ∧
    -Real.log (800 / 1451) ≤ (297698263 / 500000000) := by
  have h := checkLog_sound (w := (651 / 2251)) (n := 12)
    (lo := (23815861 / 40000000)) (hi := (297698263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1451 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1451 / 800) = 1/(800 / 1451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (23815861 / 40000000) (297698263 / 500000000) (Real.log (1451 / 800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1451 / 800) = -Real.log (800 / 1451) := by
    rw [show ((1451 / 800) : ℝ) = ((800 / 1451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (84033271 / 50000000) ≤ -Real.log (149 / 800) ∧
    -Real.log (149 / 800) ≤ (1680665423 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 349)) (n := 12)
    (lo := (14718553 / 50000000)) (hi := (294371061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 149) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 149) = 1/(149 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1680665423 / 1000000000) (-84033271 / 50000000) (Real.log (149 / 800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11842351 / 20000000) ≤ -Real.log (640 / 1157) ∧
    -Real.log (640 / 1157) ≤ (592117551 / 1000000000) := by
  have h := checkLog_sound (w := (517 / 1797)) (n := 12)
    (lo := (11842351 / 20000000)) (hi := (592117551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157 / 640) = 1/(640 / 1157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11842351 / 20000000) (592117551 / 1000000000) (Real.log (1157 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1157 / 640) = -Real.log (640 / 1157) := by
    rw [show ((1157 / 640) : ℝ) = ((640 / 1157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1649283819 / 1000000000) ≤ -Real.log (123 / 640) ∧
    -Real.log (123 / 640) ≤ (824641911 / 500000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 123) = 1/(123 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-824641911 / 500000000) (-1649283819 / 1000000000) (Real.log (123 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (97409019 / 200000000) ≤ -Real.log (400 / 651) ∧
    -Real.log (400 / 651) ≤ (60880637 / 125000000) := by
  have h := checkLog_sound (w := (251 / 1051)) (n := 12)
    (lo := (97409019 / 200000000)) (hi := (60880637 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651 / 400) = 1/(400 / 651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (97409019 / 200000000) (60880637 / 125000000) (Real.log (651 / 400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (651 / 400) = -Real.log (400 / 651) := by
    rw [show ((651 / 400) : ℝ) = ((400 / 651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6171989 / 6250000) ≤ -Real.log (149 / 400) ∧
    -Real.log (149 / 400) ≤ (493759121 / 500000000) := by
  have h := checkLog_sound (w := (51 / 349)) (n := 12)
    (lo := (14718553 / 50000000)) (hi := (294371061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 149) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 149) = 1/(149 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-493759121 / 500000000) (-6171989 / 6250000) (Real.log (149 / 400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (239860939 / 500000000) ≤ -Real.log (320 / 517) ∧
    -Real.log (320 / 517) ≤ (479721879 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 837)) (n := 12)
    (lo := (239860939 / 500000000)) (hi := (479721879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(517 / 320) = 1/(320 / 517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (239860939 / 500000000) (479721879 / 1000000000) (Real.log (517 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (517 / 320) = -Real.log (320 / 517) := by
    rw [show ((517 / 320) : ℝ) = ((320 / 517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (956136639 / 1000000000) ≤ -Real.log (123 / 320) ∧
    -Real.log (123 / 320) ≤ (956136641 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 123) = 1/(123 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-956136641 / 1000000000) (-956136639 / 1000000000) (Real.log (123 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (624251447 / 1000000000) ≤ -Real.log (31250 / 58339) ∧
    -Real.log (31250 / 58339) ≤ (78031431 / 125000000) := by
  have h := checkLog_sound (w := (27089 / 89589)) (n := 12)
    (lo := (624251447 / 1000000000)) (hi := (78031431 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58339 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58339 / 31250) = 1/(31250 / 58339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (624251447 / 1000000000) (78031431 / 125000000) (Real.log (58339 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (58339 / 31250) = -Real.log (31250 / 58339) := by
    rw [show ((58339 / 31250) : ℝ) = ((31250 / 58339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (403252789 / 200000000) ≤ -Real.log (4161 / 31250) ∧
    -Real.log (4161 / 31250) ≤ (504065987 / 250000000) := by
  have h := checkLog_sound (w := (7303 / 23947)) (n := 12)
    (lo := (125993917 / 200000000)) (hi := (314984793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8322) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 8322) = 1/(4161 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-504065987 / 250000000) (-403252789 / 200000000) (Real.log (4161 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (625994579 / 1000000000) ≤ -Real.log (200000 / 374021) ∧
    -Real.log (200000 / 374021) ≤ (31299729 / 50000000) := by
  have h := checkLog_sound (w := (174021 / 574021)) (n := 12)
    (lo := (625994579 / 1000000000)) (hi := (31299729 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374021 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374021 / 200000) = 1/(200000 / 374021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (625994579 / 1000000000) (31299729 / 50000000) (Real.log (374021 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (374021 / 200000) = -Real.log (200000 / 374021) := by
    rw [show ((374021 / 200000) : ℝ) = ((200000 / 374021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1020514423 / 500000000) ≤ -Real.log (25979 / 200000) ∧
    -Real.log (25979 / 200000) ≤ (2041028849 / 1000000000) := by
  have h := checkLog_sound (w := (24021 / 75979)) (n := 12)
    (lo := (327367243 / 500000000)) (hi := (654734487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 25979) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 25979) = 1/(25979 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2041028849 / 1000000000) (-1020514423 / 500000000) (Real.log (25979 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (19320367 / 31250000) ≤ -Real.log (1000000 / 1855681) ∧
    -Real.log (1000000 / 1855681) ≤ (123650349 / 200000000) := by
  have h := checkLog_sound (w := (855681 / 2855681)) (n := 12)
    (lo := (19320367 / 31250000)) (hi := (123650349 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1855681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1855681 / 1000000) = 1/(1000000 / 1855681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (19320367 / 31250000) (123650349 / 200000000) (Real.log (1855681 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1855681 / 1000000) = -Real.log (1000000 / 1855681) := by
    rw [show ((1855681 / 1000000) : ℝ) = ((1000000 / 1855681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (38714583 / 20000000) ≤ -Real.log (144319 / 1000000) ∧
    -Real.log (144319 / 1000000) ≤ (1935729153 / 1000000000) := by
  have h := checkLog_sound (w := (105681 / 394319)) (n := 12)
    (lo := (54943479 / 100000000)) (hi := (549434791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 144319) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 144319) = 1/(144319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1935729153 / 1000000000) (-38714583 / 20000000) (Real.log (144319 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (31022211 / 50000000) ≤ -Real.log (500000 / 929877) ∧
    -Real.log (500000 / 929877) ≤ (620444221 / 1000000000) := by
  have h := checkLog_sound (w := (429877 / 1429877)) (n := 12)
    (lo := (31022211 / 50000000)) (hi := (620444221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((929877 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(929877 / 500000) = 1/(500000 / 929877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (31022211 / 50000000) (620444221 / 1000000000) (Real.log (929877 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (929877 / 500000) = -Real.log (500000 / 929877) := by
    rw [show ((929877 / 500000) : ℝ) = ((500000 / 929877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (982178627 / 500000000) ≤ -Real.log (70123 / 500000) ∧
    -Real.log (70123 / 500000) ≤ (1964357257 / 1000000000) := by
  have h := checkLog_sound (w := (54877 / 195123)) (n := 12)
    (lo := (289031447 / 500000000)) (hi := (115612579 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 70123) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 70123) = 1/(70123 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1964357257 / 1000000000) (-982178627 / 500000000) (Real.log (70123 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2640515391 / 1000000000) ≤ -Real.log (500000000000 / 7010213890891) ∧
    -Real.log (500000000000 / 7010213890891) ≤ (528103079 / 200000000) := by
  have h := checkLog_sound (w := (3010213890891 / 11010213890891)) (n := 12)
    (lo := (561073851 / 1000000000)) (hi := (140268463 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7010213890891 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7010213890891 / 4000000000000) = 1/(500000000000 / 7010213890891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2640515391 / 1000000000) (528103079 / 200000000) (Real.log (7010213890891 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7010213890891 / 500000000000) = -Real.log (500000000000 / 7010213890891) := by
    rw [show ((7010213890891 / 500000000000) : ℝ) = ((500000000000 / 7010213890891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (41672241 / 15625000) ≤ -Real.log (500000000000 / 7198525732323) ∧
    -Real.log (500000000000 / 7198525732323) ≤ (666755857 / 250000000) := by
  have h := checkLog_sound (w := (3198525732323 / 11198525732323)) (n := 12)
    (lo := (146895471 / 250000000)) (hi := (117516377 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7198525732323 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7198525732323 / 4000000000000) = 1/(500000000000 / 7198525732323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (41672241 / 15625000) (666755857 / 250000000) (Real.log (7198525732323 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7198525732323 / 500000000000) = -Real.log (500000000000 / 7198525732323) := by
    rw [show ((7198525732323 / 500000000000) : ℝ) = ((500000000000 / 7198525732323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1276990447 / 500000000) ≤ -Real.log (500000000000 / 6429094575211) ∧
    -Real.log (500000000000 / 6429094575211) ≤ (1276990449 / 500000000) := by
  have h := checkLog_sound (w := (2429094575211 / 10429094575211)) (n := 12)
    (lo := (237269677 / 500000000)) (hi := (94907871 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6429094575211 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6429094575211 / 4000000000000) = 1/(500000000000 / 6429094575211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1276990447 / 500000000) (1276990449 / 500000000) (Real.log (6429094575211 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6429094575211 / 500000000000) = -Real.log (500000000000 / 6429094575211) := by
    rw [show ((6429094575211 / 500000000000) : ℝ) = ((500000000000 / 6429094575211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1292400737 / 500000000) ≤ -Real.log (500000000000 / 6630328137701) ∧
    -Real.log (500000000000 / 6630328137701) ≤ (1292400739 / 500000000) := by
  have h := checkLog_sound (w := (2630328137701 / 10630328137701)) (n := 12)
    (lo := (252679967 / 500000000)) (hi := (101071987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6630328137701 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6630328137701 / 4000000000000) = 1/(500000000000 / 6630328137701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1292400737 / 500000000) (1292400739 / 500000000) (Real.log (6630328137701 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6630328137701 / 500000000000) = -Real.log (500000000000 / 6630328137701) := by
    rw [show ((6630328137701 / 500000000000) : ℝ) = ((500000000000 / 6630328137701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0199
