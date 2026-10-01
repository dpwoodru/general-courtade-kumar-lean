import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0028
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

theorem reflection_log_1_neg : (85140873 / 125000000) ≤ -Real.log (102400 / 202353) ∧
    -Real.log (102400 / 202353) ≤ (136225397 / 200000000) := by
  have h := checkLog_sound (w := (99953 / 304753)) (n := 12)
    (lo := (85140873 / 125000000)) (hi := (136225397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202353 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202353 / 102400) = 1/(102400 / 202353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (85140873 / 125000000) (136225397 / 200000000) (Real.log (202353 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202353 / 102400) = -Real.log (102400 / 202353) := by
    rw [show ((202353 / 102400) : ℝ) = ((102400 / 202353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (149360957 / 40000000) ≤ -Real.log (2447 / 102400) ∧
    -Real.log (2447 / 102400) ≤ (3734023931 / 1000000000) := by
  have h := checkLog_sound (w := (753 / 5647)) (n := 12)
    (lo := (10731521 / 40000000)) (hi := (134144013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2447) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2447) = 1/(2447 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3734023931 / 1000000000) (-149360957 / 40000000) (Real.log (2447 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (170258271 / 250000000) ≤ -Real.log (51200 / 101167) ∧
    -Real.log (51200 / 101167) ≤ (136206617 / 200000000) := by
  have h := checkLog_sound (w := (49967 / 152367)) (n := 12)
    (lo := (170258271 / 250000000)) (hi := (136206617 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101167 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101167 / 51200) = 1/(51200 / 101167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (170258271 / 250000000) (136206617 / 200000000) (Real.log (101167 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101167 / 51200) = -Real.log (51200 / 101167) := by
    rw [show ((101167 / 51200) : ℝ) = ((51200 / 101167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (745257861 / 200000000) ≤ -Real.log (1233 / 51200) ∧
    -Real.log (1233 / 51200) ≤ (3726289311 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 2833)) (n := 12)
    (lo := (52110681 / 200000000)) (hi := (130276703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1233) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1233) = 1/(1233 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3726289311 / 1000000000) (-745257861 / 200000000) (Real.log (1233 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (668960543 / 1000000000) ≤ -Real.log (51200 / 99953) ∧
    -Real.log (51200 / 99953) ≤ (20905017 / 31250000) := by
  have h := checkLog_sound (w := (48753 / 151153)) (n := 12)
    (lo := (668960543 / 1000000000)) (hi := (20905017 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99953 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99953 / 51200) = 1/(51200 / 99953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (668960543 / 1000000000) (20905017 / 31250000) (Real.log (99953 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99953 / 51200) = -Real.log (51200 / 99953) := by
    rw [show ((99953 / 51200) : ℝ) = ((51200 / 99953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (608175349 / 200000000) ≤ -Real.log (2447 / 51200) ∧
    -Real.log (2447 / 51200) ≤ (12163507 / 4000000) := by
  have h := checkLog_sound (w := (753 / 5647)) (n := 12)
    (lo := (10731521 / 40000000)) (hi := (134144013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2447) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2447) = 1/(2447 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-12163507 / 4000000) (-608175349 / 200000000) (Real.log (2447 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (167192609 / 250000000) ≤ -Real.log (25600 / 49967) ∧
    -Real.log (25600 / 49967) ≤ (668770437 / 1000000000) := by
  have h := checkLog_sound (w := (24367 / 75567)) (n := 12)
    (lo := (167192609 / 250000000)) (hi := (668770437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49967 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49967 / 25600) = 1/(25600 / 49967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (167192609 / 250000000) (668770437 / 1000000000) (Real.log (49967 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49967 / 25600) = -Real.log (25600 / 49967) := by
    rw [show ((49967 / 25600) : ℝ) = ((25600 / 49967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (24265137 / 8000000) ≤ -Real.log (1233 / 25600) ∧
    -Real.log (1233 / 25600) ≤ (303314213 / 100000000) := by
  have h := checkLog_sound (w := (367 / 2833)) (n := 12)
    (lo := (52110681 / 200000000)) (hi := (130276703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1233) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1233) = 1/(1233 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-303314213 / 100000000) (-24265137 / 8000000) (Real.log (1233 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85366081 / 125000000) ≤ -Real.log (1000000 / 1979667) ∧
    -Real.log (1000000 / 1979667) ≤ (682928649 / 1000000000) := by
  have h := checkLog_sound (w := (979667 / 2979667)) (n := 12)
    (lo := (85366081 / 125000000)) (hi := (682928649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979667 / 1000000) = 1/(1000000 / 1979667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85366081 / 125000000) (682928649 / 1000000000) (Real.log (1979667 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1979667 / 1000000) = -Real.log (1000000 / 1979667) := by
    rw [show ((1979667 / 1000000) : ℝ) = ((1000000 / 1979667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1947755047 / 500000000) ≤ -Real.log (20333 / 1000000) ∧
    -Real.log (20333 / 1000000) ≤ (38955101 / 10000000) := by
  have h := checkLog_sound (w := (10917 / 51583)) (n := 12)
    (lo := (214887097 / 500000000)) (hi := (85954839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20333) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20333) = 1/(20333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-38955101 / 10000000) (-1947755047 / 500000000) (Real.log (20333 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (683004921 / 1000000000) ≤ -Real.log (500000 / 989909) ∧
    -Real.log (500000 / 989909) ≤ (341502461 / 500000000) := by
  have h := checkLog_sound (w := (489909 / 1489909)) (n := 12)
    (lo := (683004921 / 1000000000)) (hi := (341502461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989909 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989909 / 500000) = 1/(500000 / 989909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (683004921 / 1000000000) (341502461 / 500000000) (Real.log (989909 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (989909 / 500000) = -Real.log (500000 / 989909) := by
    rw [show ((989909 / 500000) : ℝ) = ((500000 / 989909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1951482079 / 500000000) ≤ -Real.log (10091 / 500000) ∧
    -Real.log (10091 / 500000) ≤ (975741041 / 250000000) := by
  have h := checkLog_sound (w := (2767 / 12858)) (n := 12)
    (lo := (218614129 / 500000000)) (hi := (437228259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10091) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10091) = 1/(10091 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-975741041 / 250000000) (-1951482079 / 500000000) (Real.log (10091 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (68288167 / 100000000) ≤ -Real.log (500000 / 989787) ∧
    -Real.log (500000 / 989787) ≤ (682881671 / 1000000000) := by
  have h := checkLog_sound (w := (489787 / 1489787)) (n := 12)
    (lo := (68288167 / 100000000)) (hi := (682881671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989787 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989787 / 500000) = 1/(500000 / 989787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (68288167 / 100000000) (682881671 / 1000000000) (Real.log (989787 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (989787 / 500000) = -Real.log (500000 / 989787) := by
    rw [show ((989787 / 500000) : ℝ) = ((500000 / 989787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3890946677 / 1000000000) ≤ -Real.log (10213 / 500000) ∧
    -Real.log (10213 / 500000) ≤ (3890946683 / 1000000000) := by
  have h := checkLog_sound (w := (2706 / 12919)) (n := 12)
    (lo := (425210777 / 1000000000)) (hi := (212605389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10213) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10213) = 1/(10213 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3890946683 / 1000000000) (-3890946677 / 1000000000) (Real.log (10213 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (170739739 / 250000000) ≤ -Real.log (1000000 / 1979727) ∧
    -Real.log (1000000 / 1979727) ≤ (682958957 / 1000000000) := by
  have h := checkLog_sound (w := (979727 / 2979727)) (n := 12)
    (lo := (170739739 / 250000000)) (hi := (682958957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979727 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979727 / 1000000) = 1/(1000000 / 1979727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (170739739 / 250000000) (682958957 / 1000000000) (Real.log (1979727 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1979727 / 1000000) = -Real.log (1000000 / 1979727) := by
    rw [show ((1979727 / 1000000) : ℝ) = ((1000000 / 1979727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (974616331 / 250000000) ≤ -Real.log (20273 / 1000000) ∧
    -Real.log (20273 / 1000000) ≤ (389846533 / 100000000) := by
  have h := checkLog_sound (w := (10977 / 51523)) (n := 12)
    (lo := (27045589 / 62500000)) (hi := (17309177 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20273) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20273) = 1/(20273 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-389846533 / 100000000) (-974616331 / 250000000) (Real.log (20273 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2289219371 / 500000000) ≤ -Real.log (62500000000 / 6085141764619) ∧
    -Real.log (62500000000 / 6085141764619) ≤ (4578438749 / 1000000000) := by
  have h := checkLog_sound (w := (2085141764619 / 10085141764619)) (n := 12)
    (lo := (209777831 / 500000000)) (hi := (419555663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6085141764619 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6085141764619 / 4000000000000) = 1/(62500000000 / 6085141764619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2289219371 / 500000000) (4578438749 / 1000000000) (Real.log (6085141764619 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6085141764619 / 62500000000) = -Real.log (62500000000 / 6085141764619) := by
    rw [show ((6085141764619 / 62500000000) : ℝ) = ((62500000000 / 6085141764619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2292984539 / 500000000) ≤ -Real.log (500000000000 / 49049103161233) ∧
    -Real.log (500000000000 / 49049103161233) ≤ (917193817 / 200000000) := by
  have h := checkLog_sound (w := (17049103161233 / 81049103161233)) (n := 12)
    (lo := (213542999 / 500000000)) (hi := (427085999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49049103161233 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(49049103161233 / 32000000000000) = 1/(500000000000 / 49049103161233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2292984539 / 500000000) (917193817 / 200000000) (Real.log (49049103161233 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (49049103161233 / 500000000000) = -Real.log (500000000000 / 49049103161233) := by
    rw [show ((49049103161233 / 500000000000) : ℝ) = ((500000000000 / 49049103161233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2286914173 / 500000000) ≤ -Real.log (250000000000 / 24228605698619) ∧
    -Real.log (250000000000 / 24228605698619) ≤ (4573828353 / 1000000000) := by
  have h := checkLog_sound (w := (8228605698619 / 40228605698619)) (n := 12)
    (lo := (207472633 / 500000000)) (hi := (414945267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24228605698619 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(24228605698619 / 16000000000000) = 1/(250000000000 / 24228605698619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2286914173 / 500000000) (4573828353 / 1000000000) (Real.log (24228605698619 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (24228605698619 / 250000000000) = -Real.log (250000000000 / 24228605698619) := by
    rw [show ((24228605698619 / 250000000000) : ℝ) = ((250000000000 / 24228605698619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (114535607 / 25000000) ≤ -Real.log (500000000000 / 48826690672323) ∧
    -Real.log (500000000000 / 48826690672323) ≤ (4581424287 / 1000000000) := by
  have h := checkLog_sound (w := (16826690672323 / 80826690672323)) (n := 12)
    (lo := (1056353 / 2500000)) (hi := (422541201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48826690672323 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(48826690672323 / 32000000000000) = 1/(500000000000 / 48826690672323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (114535607 / 25000000) (4581424287 / 1000000000) (Real.log (48826690672323 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (48826690672323 / 500000000000) = -Real.log (500000000000 / 48826690672323) := by
    rw [show ((48826690672323 / 500000000000) : ℝ) = ((500000000000 / 48826690672323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0028
