import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1728_neg : (85309553 / 1000000000) ≤ -Real.log (229557 / 250000) ∧
    -Real.log (229557 / 250000) ≤ (42654777 / 500000000) := by
  have h := checkLog_sound (w := (20443 / 479557)) (n := 12)
    (lo := (85309553 / 1000000000)) (hi := (42654777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229557) = 1/(229557 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1728 : Bounds (-42654777 / 500000000) (-85309553 / 1000000000) (Real.log (229557 / 250000)) := by
  have h := reflection_log_1728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1729_neg : (1341823 / 200000000) ≤ -Real.log (62082083751 / 62500000000) ∧
    -Real.log (62082083751 / 62500000000) ≤ (1677279 / 250000000) := by
  have h := checkLog_sound (w := (417916249 / 124582083751)) (n := 12)
    (lo := (1341823 / 200000000)) (hi := (1677279 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62082083751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62082083751) = 1/(62082083751 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1729 : Bounds (-1677279 / 250000000) (-1341823 / 200000000) (Real.log (62082083751 / 62500000000)) := by
  have h := reflection_log_1729_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1730_neg : (1668523 / 250000000) ≤ -Real.log (993348129519 / 1000000000000) ∧
    -Real.log (993348129519 / 1000000000000) ≤ (6674093 / 1000000000) := by
  have h := checkLog_sound (w := (6651870481 / 1993348129519)) (n := 12)
    (lo := (1668523 / 250000000)) (hi := (6674093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993348129519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993348129519) = 1/(993348129519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1730 : Bounds (-6674093 / 1000000000) (-1668523 / 250000000) (Real.log (993348129519 / 1000000000000)) := by
  have h := reflection_log_1730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1731_neg : (16348113 / 100000000) ≤ -Real.log (500000000000 / 588801567003) ∧
    -Real.log (500000000000 / 588801567003) ≤ (163481131 / 1000000000) := by
  have h := checkLog_sound (w := (88801567003 / 1088801567003)) (n := 12)
    (lo := (16348113 / 100000000)) (hi := (163481131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588801567003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588801567003 / 500000000000) = 1/(500000000000 / 588801567003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1731 : Bounds (16348113 / 100000000) (163481131 / 1000000000) (Real.log (588801567003 / 500000000000)) := by
  have h := reflection_log_1731_neg
  have he : Real.log (588801567003 / 500000000000) = -Real.log (500000000000 / 588801567003) := by
    rw [show ((588801567003 / 500000000000) : ℝ) = ((500000000000 / 588801567003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1732_neg : (16390999 / 100000000) ≤ -Real.log (500000000000 / 589054134703) ∧
    -Real.log (500000000000 / 589054134703) ≤ (163909991 / 1000000000) := by
  have h := checkLog_sound (w := (89054134703 / 1089054134703)) (n := 12)
    (lo := (16390999 / 100000000)) (hi := (163909991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589054134703 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589054134703 / 500000000000) = 1/(500000000000 / 589054134703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1732 : Bounds (16390999 / 100000000) (163909991 / 1000000000) (Real.log (589054134703 / 500000000000)) := by
  have h := reflection_log_1732_neg
  have he : Real.log (589054134703 / 500000000000) = -Real.log (500000000000 / 589054134703) := by
    rw [show ((589054134703 / 500000000000) : ℝ) = ((500000000000 / 589054134703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1733_neg : (327906873 / 1000000000) ≤ -Real.log (250000000000 / 347014925373) ∧
    -Real.log (250000000000 / 347014925373) ≤ (163953437 / 500000000) := by
  have h := checkLog_sound (w := (97014925373 / 597014925373)) (n := 12)
    (lo := (327906873 / 1000000000)) (hi := (163953437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347014925373 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347014925373 / 250000000000) = 1/(250000000000 / 347014925373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1733 : Bounds (327906873 / 1000000000) (163953437 / 500000000) (Real.log (347014925373 / 250000000000)) := by
  have h := reflection_log_1733_neg
  have he : Real.log (347014925373 / 250000000000) = -Real.log (250000000000 / 347014925373) := by
    rw [show ((347014925373 / 250000000000) : ℝ) = ((250000000000 / 347014925373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1734_neg : (328112301 / 1000000000) ≤ -Real.log (500000000000 / 694172438501) ∧
    -Real.log (500000000000 / 694172438501) ≤ (164056151 / 500000000) := by
  have h := checkLog_sound (w := (194172438501 / 1194172438501)) (n := 12)
    (lo := (328112301 / 1000000000)) (hi := (164056151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694172438501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694172438501 / 500000000000) = 1/(500000000000 / 694172438501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1734 : Bounds (328112301 / 1000000000) (164056151 / 500000000) (Real.log (694172438501 / 500000000000)) := by
  have h := reflection_log_1734_neg
  have he : Real.log (694172438501 / 500000000000) = -Real.log (500000000000 / 694172438501) := by
    rw [show ((694172438501 / 500000000000) : ℝ) = ((500000000000 / 694172438501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1735_neg : (75372443 / 500000000) ≤ -Real.log (10000 / 11627) ∧
    -Real.log (10000 / 11627) ≤ (150744887 / 1000000000) := by
  have h := checkLog_sound (w := (1627 / 21627)) (n := 12)
    (lo := (75372443 / 500000000)) (hi := (150744887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11627 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11627 / 10000) = 1/(10000 / 11627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1735 : Bounds (75372443 / 500000000) (150744887 / 1000000000) (Real.log (11627 / 10000)) := by
  have h := reflection_log_1735_neg
  have he : Real.log (11627 / 10000) = -Real.log (10000 / 11627) := by
    rw [show ((11627 / 10000) : ℝ) = ((10000 / 11627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1736_neg : (177572849 / 1000000000) ≤ -Real.log (8373 / 10000) ∧
    -Real.log (8373 / 10000) ≤ (3551457 / 20000000) := by
  have h := checkLog_sound (w := (1627 / 18373)) (n := 12)
    (lo := (177572849 / 1000000000)) (hi := (3551457 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8373) = 1/(8373 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1736 : Bounds (-3551457 / 20000000) (-177572849 / 1000000000) (Real.log (8373 / 10000)) := by
  have h := reflection_log_1736_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1737_neg : (81343 / 500000000) ≤ -Real.log (10000000 / 10001627) ∧
    -Real.log (10000000 / 10001627) ≤ (162687 / 1000000000) := by
  have h := checkLog_sound (w := (1627 / 20001627)) (n := 12)
    (lo := (81343 / 500000000)) (hi := (162687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001627 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001627 / 10000000) = 1/(10000000 / 10001627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1737 : Bounds (81343 / 500000000) (162687 / 1000000000) (Real.log (10001627 / 10000000)) := by
  have h := reflection_log_1737_neg
  have he : Real.log (10001627 / 10000000) = -Real.log (10000000 / 10001627) := by
    rw [show ((10001627 / 10000000) : ℝ) = ((10000000 / 10001627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1738_neg : (162713 / 1000000000) ≤ -Real.log (9998373 / 10000000) ∧
    -Real.log (9998373 / 10000000) ≤ (81357 / 500000000) := by
  have h := checkLog_sound (w := (1627 / 19998373)) (n := 12)
    (lo := (162713 / 1000000000)) (hi := (81357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998373) = 1/(9998373 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1738 : Bounds (-81357 / 500000000) (-162713 / 1000000000) (Real.log (9998373 / 10000000)) := by
  have h := reflection_log_1738_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1739_neg : (78449747 / 1000000000) ≤ -Real.log (1000000 / 1081609) ∧
    -Real.log (1000000 / 1081609) ≤ (19612437 / 250000000) := by
  have h := checkLog_sound (w := (81609 / 2081609)) (n := 12)
    (lo := (78449747 / 1000000000)) (hi := (19612437 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081609 / 1000000) = 1/(1000000 / 1081609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1739 : Bounds (78449747 / 1000000000) (19612437 / 250000000) (Real.log (1081609 / 1000000)) := by
  have h := reflection_log_1739_neg
  have he : Real.log (1081609 / 1000000) = -Real.log (1000000 / 1081609) := by
    rw [show ((1081609 / 1000000) : ℝ) = ((1000000 / 1081609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1740_neg : (85132053 / 1000000000) ≤ -Real.log (918391 / 1000000) ∧
    -Real.log (918391 / 1000000) ≤ (42566027 / 500000000) := by
  have h := checkLog_sound (w := (81609 / 1918391)) (n := 12)
    (lo := (85132053 / 1000000000)) (hi := (42566027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918391) = 1/(918391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1740 : Bounds (-42566027 / 500000000) (-85132053 / 1000000000) (Real.log (918391 / 1000000)) := by
  have h := reflection_log_1740_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1741_neg : (78647581 / 1000000000) ≤ -Real.log (1000000 / 1081823) ∧
    -Real.log (1000000 / 1081823) ≤ (39323791 / 500000000) := by
  have h := checkLog_sound (w := (81823 / 2081823)) (n := 12)
    (lo := (78647581 / 1000000000)) (hi := (39323791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081823 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081823 / 1000000) = 1/(1000000 / 1081823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1741 : Bounds (78647581 / 1000000000) (39323791 / 500000000) (Real.log (1081823 / 1000000)) := by
  have h := reflection_log_1741_neg
  have he : Real.log (1081823 / 1000000) = -Real.log (1000000 / 1081823) := by
    rw [show ((1081823 / 1000000) : ℝ) = ((1000000 / 1081823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1742_neg : (10670637 / 125000000) ≤ -Real.log (918177 / 1000000) ∧
    -Real.log (918177 / 1000000) ≤ (85365097 / 1000000000) := by
  have h := checkLog_sound (w := (81823 / 1918177)) (n := 12)
    (lo := (10670637 / 125000000)) (hi := (85365097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918177) = 1/(918177 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1742 : Bounds (-85365097 / 1000000000) (-10670637 / 125000000) (Real.log (918177 / 1000000)) := by
  have h := reflection_log_1742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1743_neg : (1343503 / 200000000) ≤ -Real.log (993304996671 / 1000000000000) ∧
    -Real.log (993304996671 / 1000000000000) ≤ (1679379 / 250000000) := by
  have h := checkLog_sound (w := (6695003329 / 1993304996671)) (n := 12)
    (lo := (1343503 / 200000000)) (hi := (1679379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993304996671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993304996671) = 1/(993304996671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1743 : Bounds (-1679379 / 250000000) (-1343503 / 200000000) (Real.log (993304996671 / 1000000000000)) := by
  have h := reflection_log_1743_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1744_neg : (1336461 / 200000000) ≤ -Real.log (993339971119 / 1000000000000) ∧
    -Real.log (993339971119 / 1000000000000) ≤ (3341153 / 500000000) := by
  have h := checkLog_sound (w := (6660028881 / 1993339971119)) (n := 12)
    (lo := (1336461 / 200000000)) (hi := (3341153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993339971119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993339971119) = 1/(993339971119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1744 : Bounds (-3341153 / 500000000) (-1336461 / 200000000) (Real.log (993339971119 / 1000000000000)) := by
  have h := reflection_log_1744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1745_neg : (817909 / 5000000) ≤ -Real.log (3906250000 / 4600475349) ∧
    -Real.log (3906250000 / 4600475349) ≤ (163581801 / 1000000000) := by
  have h := checkLog_sound (w := (694225349 / 8506725349)) (n := 12)
    (lo := (817909 / 5000000)) (hi := (163581801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4600475349 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4600475349 / 3906250000) = 1/(3906250000 / 4600475349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1745 : Bounds (817909 / 5000000) (163581801 / 1000000000) (Real.log (4600475349 / 3906250000)) := by
  have h := reflection_log_1745_neg
  have he : Real.log (4600475349 / 3906250000) = -Real.log (3906250000 / 4600475349) := by
    rw [show ((4600475349 / 3906250000) : ℝ) = ((3906250000 / 4600475349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1746_neg : (164012677 / 1000000000) ≤ -Real.log (244140625 / 287653626) ∧
    -Real.log (244140625 / 287653626) ≤ (82006339 / 500000000) := by
  have h := checkLog_sound (w := (43513001 / 531794251)) (n := 12)
    (lo := (164012677 / 1000000000)) (hi := (82006339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287653626 / 244140625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287653626 / 244140625) = 1/(244140625 / 287653626) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1746 : Bounds (164012677 / 1000000000) (82006339 / 500000000) (Real.log (287653626 / 244140625)) := by
  have h := reflection_log_1746_neg
  have he : Real.log (287653626 / 244140625) = -Real.log (244140625 / 287653626) := by
    rw [show ((287653626 / 244140625) : ℝ) = ((244140625 / 287653626) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1747_neg : (328112301 / 1000000000) ≤ -Real.log (1000000000 / 1388344877) ∧
    -Real.log (1000000000 / 1388344877) ≤ (164056151 / 500000000) := by
  have h := checkLog_sound (w := (388344877 / 2388344877)) (n := 12)
    (lo := (328112301 / 1000000000)) (hi := (164056151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1388344877 / 1000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1388344877 / 1000000000) = 1/(1000000000 / 1388344877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1747 : Bounds (328112301 / 1000000000) (164056151 / 500000000) (Real.log (1388344877 / 1000000000)) := by
  have h := reflection_log_1747_neg
  have he : Real.log (1388344877 / 1000000000) = -Real.log (1000000000 / 1388344877) := by
    rw [show ((1388344877 / 1000000000) : ℝ) = ((1000000000 / 1388344877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1748_neg : (41039717 / 125000000) ≤ -Real.log (500000000000 / 694315060313) ∧
    -Real.log (500000000000 / 694315060313) ≤ (328317737 / 1000000000) := by
  have h := checkLog_sound (w := (194315060313 / 1194315060313)) (n := 12)
    (lo := (41039717 / 125000000)) (hi := (328317737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694315060313 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694315060313 / 500000000000) = 1/(500000000000 / 694315060313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1748 : Bounds (41039717 / 125000000) (328317737 / 1000000000) (Real.log (694315060313 / 500000000000)) := by
  have h := reflection_log_1748_neg
  have he : Real.log (694315060313 / 500000000000) = -Real.log (500000000000 / 694315060313) := by
    rw [show ((694315060313 / 500000000000) : ℝ) = ((500000000000 / 694315060313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1749_neg : (150830889 / 1000000000) ≤ -Real.log (2500 / 2907) ∧
    -Real.log (2500 / 2907) ≤ (15083089 / 100000000) := by
  have h := checkLog_sound (w := (407 / 5407)) (n := 12)
    (lo := (150830889 / 1000000000)) (hi := (15083089 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2907 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2907 / 2500) = 1/(2500 / 2907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1749 : Bounds (150830889 / 1000000000) (15083089 / 100000000) (Real.log (2907 / 2500)) := by
  have h := reflection_log_1749_neg
  have he : Real.log (2907 / 2500) = -Real.log (2500 / 2907) := by
    rw [show ((2907 / 2500) : ℝ) = ((2500 / 2907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1750_neg : (1388221 / 7812500) ≤ -Real.log (2093 / 2500) ∧
    -Real.log (2093 / 2500) ≤ (177692289 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 4593)) (n := 12)
    (lo := (1388221 / 7812500)) (hi := (177692289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2093) = 1/(2093 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1750 : Bounds (-177692289 / 1000000000) (-1388221 / 7812500) (Real.log (2093 / 2500)) := by
  have h := reflection_log_1750_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1751_neg : (81393 / 500000000) ≤ -Real.log (2500000 / 2500407) ∧
    -Real.log (2500000 / 2500407) ≤ (162787 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 5000407)) (n := 12)
    (lo := (81393 / 500000000)) (hi := (162787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500407 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500407 / 2500000) = 1/(2500000 / 2500407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1751 : Bounds (81393 / 500000000) (162787 / 1000000000) (Real.log (2500407 / 2500000)) := by
  have h := reflection_log_1751_neg
  have he : Real.log (2500407 / 2500000) = -Real.log (2500000 / 2500407) := by
    rw [show ((2500407 / 2500000) : ℝ) = ((2500000 / 2500407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1752_neg : (162813 / 1000000000) ≤ -Real.log (2499593 / 2500000) ∧
    -Real.log (2499593 / 2500000) ≤ (81407 / 500000000) := by
  have h := checkLog_sound (w := (407 / 4999593)) (n := 12)
    (lo := (162813 / 1000000000)) (hi := (81407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499593) = 1/(2499593 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1752 : Bounds (-81407 / 500000000) (-162813 / 1000000000) (Real.log (2499593 / 2500000)) := by
  have h := reflection_log_1752_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1753_neg : (39248449 / 500000000) ≤ -Real.log (50000 / 54083) ∧
    -Real.log (50000 / 54083) ≤ (78496899 / 1000000000) := by
  have h := checkLog_sound (w := (4083 / 104083)) (n := 12)
    (lo := (39248449 / 500000000)) (hi := (78496899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54083 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54083 / 50000) = 1/(50000 / 54083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1753 : Bounds (39248449 / 500000000) (78496899 / 1000000000) (Real.log (54083 / 50000)) := by
  have h := reflection_log_1753_neg
  have he : Real.log (54083 / 50000) = -Real.log (50000 / 54083) := by
    rw [show ((54083 / 50000) : ℝ) = ((50000 / 54083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1754_neg : (42593793 / 500000000) ≤ -Real.log (45917 / 50000) ∧
    -Real.log (45917 / 50000) ≤ (85187587 / 1000000000) := by
  have h := checkLog_sound (w := (4083 / 95917)) (n := 12)
    (lo := (42593793 / 500000000)) (hi := (85187587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45917) = 1/(45917 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1754 : Bounds (-85187587 / 1000000000) (-42593793 / 500000000) (Real.log (45917 / 50000)) := by
  have h := reflection_log_1754_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1755_neg : (39347361 / 500000000) ≤ -Real.log (500000 / 540937) ∧
    -Real.log (500000 / 540937) ≤ (78694723 / 1000000000) := by
  have h := checkLog_sound (w := (40937 / 1040937)) (n := 12)
    (lo := (39347361 / 500000000)) (hi := (78694723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540937 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(540937 / 500000) = 1/(500000 / 540937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1755 : Bounds (39347361 / 500000000) (78694723 / 1000000000) (Real.log (540937 / 500000)) := by
  have h := reflection_log_1755_neg
  have he : Real.log (540937 / 500000) = -Real.log (500000 / 540937) := by
    rw [show ((540937 / 500000) : ℝ) = ((500000 / 540937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1756_neg : (42710321 / 500000000) ≤ -Real.log (459063 / 500000) ∧
    -Real.log (459063 / 500000) ≤ (85420643 / 1000000000) := by
  have h := checkLog_sound (w := (40937 / 959063)) (n := 12)
    (lo := (42710321 / 500000000)) (hi := (85420643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 459063) = 1/(459063 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1756 : Bounds (-85420643 / 1000000000) (-42710321 / 500000000) (Real.log (459063 / 500000)) := by
  have h := reflection_log_1756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1757_neg : (42037 / 6250000) ≤ -Real.log (248324162031 / 250000000000) ∧
    -Real.log (248324162031 / 250000000000) ≤ (6725921 / 1000000000) := by
  have h := checkLog_sound (w := (1675837969 / 498324162031)) (n := 12)
    (lo := (42037 / 6250000)) (hi := (6725921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248324162031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248324162031) = 1/(248324162031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1757 : Bounds (-6725921 / 1000000000) (-42037 / 6250000) (Real.log (248324162031 / 250000000000)) := by
  have h := reflection_log_1757_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1758_neg : (52271 / 7812500) ≤ -Real.log (2483329111 / 2500000000) ∧
    -Real.log (2483329111 / 2500000000) ≤ (6690689 / 1000000000) := by
  have h := checkLog_sound (w := (16670889 / 4983329111)) (n := 12)
    (lo := (52271 / 7812500)) (hi := (6690689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2483329111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2483329111) = 1/(2483329111 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1758 : Bounds (-6690689 / 1000000000) (-52271 / 7812500) (Real.log (2483329111 / 2500000000)) := by
  have h := reflection_log_1758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1759_neg : (40921121 / 250000000) ≤ -Real.log (100000000000 / 117784262909) ∧
    -Real.log (100000000000 / 117784262909) ≤ (32736897 / 200000000) := by
  have h := checkLog_sound (w := (17784262909 / 217784262909)) (n := 12)
    (lo := (40921121 / 250000000)) (hi := (32736897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117784262909 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117784262909 / 100000000000) = 1/(100000000000 / 117784262909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1759 : Bounds (40921121 / 250000000) (32736897 / 200000000) (Real.log (117784262909 / 100000000000)) := by
  have h := reflection_log_1759_neg
  have he : Real.log (117784262909 / 100000000000) = -Real.log (100000000000 / 117784262909) := by
    rw [show ((117784262909 / 100000000000) : ℝ) = ((100000000000 / 117784262909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1760_neg : (32823073 / 200000000) ≤ -Real.log (31250000000 / 36823445257) ∧
    -Real.log (31250000000 / 36823445257) ≤ (82057683 / 500000000) := by
  have h := checkLog_sound (w := (5573445257 / 68073445257)) (n := 12)
    (lo := (32823073 / 200000000)) (hi := (82057683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36823445257 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36823445257 / 31250000000) = 1/(31250000000 / 36823445257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1760 : Bounds (32823073 / 200000000) (82057683 / 500000000) (Real.log (36823445257 / 31250000000)) := by
  have h := reflection_log_1760_neg
  have he : Real.log (36823445257 / 31250000000) = -Real.log (31250000000 / 36823445257) := by
    rw [show ((36823445257 / 31250000000) : ℝ) = ((31250000000 / 36823445257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1761_neg : (41039717 / 125000000) ≤ -Real.log (62500000000 / 86789382539) ∧
    -Real.log (62500000000 / 86789382539) ≤ (328317737 / 1000000000) := by
  have h := checkLog_sound (w := (24289382539 / 149289382539)) (n := 12)
    (lo := (41039717 / 125000000)) (hi := (328317737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86789382539 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86789382539 / 62500000000) = 1/(62500000000 / 86789382539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1761 : Bounds (41039717 / 125000000) (328317737 / 1000000000) (Real.log (86789382539 / 62500000000)) := by
  have h := reflection_log_1761_neg
  have he : Real.log (86789382539 / 62500000000) = -Real.log (62500000000 / 86789382539) := by
    rw [show ((86789382539 / 62500000000) : ℝ) = ((62500000000 / 86789382539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1762_neg : (164261589 / 500000000) ≤ -Real.log (500000000000 / 694457716197) ∧
    -Real.log (500000000000 / 694457716197) ≤ (328523179 / 1000000000) := by
  have h := checkLog_sound (w := (194457716197 / 1194457716197)) (n := 12)
    (lo := (164261589 / 500000000)) (hi := (328523179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694457716197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694457716197 / 500000000000) = 1/(500000000000 / 694457716197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1762 : Bounds (164261589 / 500000000) (328523179 / 1000000000) (Real.log (694457716197 / 500000000000)) := by
  have h := reflection_log_1762_neg
  have he : Real.log (694457716197 / 500000000000) = -Real.log (500000000000 / 694457716197) := by
    rw [show ((694457716197 / 500000000000) : ℝ) = ((500000000000 / 694457716197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1763_neg : (30183377 / 200000000) ≤ -Real.log (10000 / 11629) ∧
    -Real.log (10000 / 11629) ≤ (75458443 / 500000000) := by
  have h := checkLog_sound (w := (1629 / 21629)) (n := 12)
    (lo := (30183377 / 200000000)) (hi := (75458443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11629 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11629 / 10000) = 1/(10000 / 11629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1763 : Bounds (30183377 / 200000000) (75458443 / 500000000) (Real.log (11629 / 10000)) := by
  have h := reflection_log_1763_neg
  have he : Real.log (11629 / 10000) = -Real.log (10000 / 11629) := by
    rw [show ((11629 / 10000) : ℝ) = ((10000 / 11629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1764_neg : (177811741 / 1000000000) ≤ -Real.log (8371 / 10000) ∧
    -Real.log (8371 / 10000) ≤ (88905871 / 500000000) := by
  have h := checkLog_sound (w := (1629 / 18371)) (n := 12)
    (lo := (177811741 / 1000000000)) (hi := (88905871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8371) = 1/(8371 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1764 : Bounds (-88905871 / 500000000) (-177811741 / 1000000000) (Real.log (8371 / 10000)) := by
  have h := reflection_log_1764_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1765_neg : (81443 / 500000000) ≤ -Real.log (10000000 / 10001629) ∧
    -Real.log (10000000 / 10001629) ≤ (162887 / 1000000000) := by
  have h := checkLog_sound (w := (1629 / 20001629)) (n := 12)
    (lo := (81443 / 500000000)) (hi := (162887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001629 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001629 / 10000000) = 1/(10000000 / 10001629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1765 : Bounds (81443 / 500000000) (162887 / 1000000000) (Real.log (10001629 / 10000000)) := by
  have h := reflection_log_1765_neg
  have he : Real.log (10001629 / 10000000) = -Real.log (10000000 / 10001629) := by
    rw [show ((10001629 / 10000000) : ℝ) = ((10000000 / 10001629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1766_neg : (162913 / 1000000000) ≤ -Real.log (9998371 / 10000000) ∧
    -Real.log (9998371 / 10000000) ≤ (81457 / 500000000) := by
  have h := checkLog_sound (w := (1629 / 19998371)) (n := 12)
    (lo := (162913 / 1000000000)) (hi := (81457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998371) = 1/(9998371 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1766 : Bounds (-81457 / 500000000) (-162913 / 1000000000) (Real.log (9998371 / 10000000)) := by
  have h := reflection_log_1766_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1767_neg : (39272023 / 500000000) ≤ -Real.log (1000000 / 1081711) ∧
    -Real.log (1000000 / 1081711) ≤ (78544047 / 1000000000) := by
  have h := checkLog_sound (w := (81711 / 2081711)) (n := 12)
    (lo := (39272023 / 500000000)) (hi := (78544047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081711 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081711 / 1000000) = 1/(1000000 / 1081711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1767 : Bounds (39272023 / 500000000) (78544047 / 1000000000) (Real.log (1081711 / 1000000)) := by
  have h := reflection_log_1767_neg
  have he : Real.log (1081711 / 1000000) = -Real.log (1000000 / 1081711) := by
    rw [show ((1081711 / 1000000) : ℝ) = ((1000000 / 1081711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1768_neg : (85243123 / 1000000000) ≤ -Real.log (918289 / 1000000) ∧
    -Real.log (918289 / 1000000) ≤ (21310781 / 250000000) := by
  have h := checkLog_sound (w := (81711 / 1918289)) (n := 12)
    (lo := (85243123 / 1000000000)) (hi := (21310781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918289) = 1/(918289 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1768 : Bounds (-21310781 / 250000000) (-85243123 / 1000000000) (Real.log (918289 / 1000000)) := by
  have h := reflection_log_1768_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1769_neg : (78740937 / 1000000000) ≤ -Real.log (250000 / 270481) ∧
    -Real.log (250000 / 270481) ≤ (39370469 / 500000000) := by
  have h := checkLog_sound (w := (20481 / 520481)) (n := 12)
    (lo := (78740937 / 1000000000)) (hi := (39370469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270481 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270481 / 250000) = 1/(250000 / 270481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1769 : Bounds (78740937 / 1000000000) (39370469 / 500000000) (Real.log (270481 / 250000)) := by
  have h := reflection_log_1769_neg
  have he : Real.log (270481 / 250000) = -Real.log (250000 / 270481) := by
    rw [show ((270481 / 250000) : ℝ) = ((250000 / 270481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1770_neg : (85475103 / 1000000000) ≤ -Real.log (229519 / 250000) ∧
    -Real.log (229519 / 250000) ≤ (2671097 / 31250000) := by
  have h := checkLog_sound (w := (20481 / 479519)) (n := 12)
    (lo := (85475103 / 1000000000)) (hi := (2671097 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229519) = 1/(229519 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1770 : Bounds (-2671097 / 31250000) (-85475103 / 1000000000) (Real.log (229519 / 250000)) := by
  have h := reflection_log_1770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1771_neg : (1346833 / 200000000) ≤ -Real.log (62080528639 / 62500000000) ∧
    -Real.log (62080528639 / 62500000000) ≤ (3367083 / 500000000) := by
  have h := checkLog_sound (w := (419471361 / 124580528639)) (n := 12)
    (lo := (1346833 / 200000000)) (hi := (3367083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62080528639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62080528639) = 1/(62080528639 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1771 : Bounds (-3367083 / 500000000) (-1346833 / 200000000) (Real.log (62080528639 / 62500000000)) := by
  have h := reflection_log_1771_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1772_neg : (1674769 / 250000000) ≤ -Real.log (993323312479 / 1000000000000) ∧
    -Real.log (993323312479 / 1000000000000) ≤ (6699077 / 1000000000) := by
  have h := checkLog_sound (w := (6676687521 / 1993323312479)) (n := 12)
    (lo := (1674769 / 250000000)) (hi := (6699077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993323312479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993323312479) = 1/(993323312479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1772 : Bounds (-6699077 / 1000000000) (-1674769 / 250000000) (Real.log (993323312479 / 1000000000000)) := by
  have h := reflection_log_1772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1773_neg : (163787169 / 1000000000) ≤ -Real.log (100000000000 / 117796358227) ∧
    -Real.log (100000000000 / 117796358227) ≤ (16378717 / 100000000) := by
  have h := checkLog_sound (w := (17796358227 / 217796358227)) (n := 12)
    (lo := (163787169 / 1000000000)) (hi := (16378717 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117796358227 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117796358227 / 100000000000) = 1/(100000000000 / 117796358227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1773 : Bounds (163787169 / 1000000000) (16378717 / 100000000) (Real.log (117796358227 / 100000000000)) := by
  have h := reflection_log_1773_neg
  have he : Real.log (117796358227 / 100000000000) = -Real.log (100000000000 / 117796358227) := by
    rw [show ((117796358227 / 100000000000) : ℝ) = ((100000000000 / 117796358227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1774_neg : (4105401 / 25000000) ≤ -Real.log (100000000000 / 117846888493) ∧
    -Real.log (100000000000 / 117846888493) ≤ (164216041 / 1000000000) := by
  have h := checkLog_sound (w := (17846888493 / 217846888493)) (n := 12)
    (lo := (4105401 / 25000000)) (hi := (164216041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117846888493 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117846888493 / 100000000000) = 1/(100000000000 / 117846888493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1774 : Bounds (4105401 / 25000000) (164216041 / 1000000000) (Real.log (117846888493 / 100000000000)) := by
  have h := reflection_log_1774_neg
  have he : Real.log (117846888493 / 100000000000) = -Real.log (100000000000 / 117846888493) := by
    rw [show ((117846888493 / 100000000000) : ℝ) = ((100000000000 / 117846888493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1775_neg : (164261589 / 500000000) ≤ -Real.log (125000000000 / 173614429049) ∧
    -Real.log (125000000000 / 173614429049) ≤ (328523179 / 1000000000) := by
  have h := checkLog_sound (w := (48614429049 / 298614429049)) (n := 12)
    (lo := (164261589 / 500000000)) (hi := (328523179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173614429049 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173614429049 / 125000000000) = 1/(125000000000 / 173614429049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1775 : Bounds (164261589 / 500000000) (328523179 / 1000000000) (Real.log (173614429049 / 125000000000)) := by
  have h := reflection_log_1775_neg
  have he : Real.log (173614429049 / 125000000000) = -Real.log (125000000000 / 173614429049) := by
    rw [show ((173614429049 / 125000000000) : ℝ) = ((125000000000 / 173614429049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1776_neg : (164364313 / 500000000) ≤ -Real.log (100000000000 / 138920081233) ∧
    -Real.log (100000000000 / 138920081233) ≤ (328728627 / 1000000000) := by
  have h := checkLog_sound (w := (38920081233 / 238920081233)) (n := 12)
    (lo := (164364313 / 500000000)) (hi := (328728627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138920081233 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138920081233 / 100000000000) = 1/(100000000000 / 138920081233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1776 : Bounds (164364313 / 500000000) (328728627 / 1000000000) (Real.log (138920081233 / 100000000000)) := by
  have h := reflection_log_1776_neg
  have he : Real.log (138920081233 / 100000000000) = -Real.log (100000000000 / 138920081233) := by
    rw [show ((138920081233 / 100000000000) : ℝ) = ((100000000000 / 138920081233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1777_neg : (151002873 / 1000000000) ≤ -Real.log (1000 / 1163) ∧
    -Real.log (1000 / 1163) ≤ (75501437 / 500000000) := by
  have h := checkLog_sound (w := (163 / 2163)) (n := 12)
    (lo := (151002873 / 1000000000)) (hi := (75501437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1163 / 1000) = 1/(1000 / 1163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1777 : Bounds (151002873 / 1000000000) (75501437 / 500000000) (Real.log (1163 / 1000)) := by
  have h := reflection_log_1777_neg
  have he : Real.log (1163 / 1000) = -Real.log (1000 / 1163) := by
    rw [show ((1163 / 1000) : ℝ) = ((1000 / 1163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1778_neg : (22241401 / 125000000) ≤ -Real.log (837 / 1000) ∧
    -Real.log (837 / 1000) ≤ (177931209 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 1837)) (n := 12)
    (lo := (22241401 / 125000000)) (hi := (177931209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 837) = 1/(837 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1778 : Bounds (-177931209 / 1000000000) (-22241401 / 125000000) (Real.log (837 / 1000)) := by
  have h := reflection_log_1778_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1779_neg : (81493 / 500000000) ≤ -Real.log (1000000 / 1000163) ∧
    -Real.log (1000000 / 1000163) ≤ (162987 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 2000163)) (n := 12)
    (lo := (81493 / 500000000)) (hi := (162987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000163 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000163 / 1000000) = 1/(1000000 / 1000163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1779 : Bounds (81493 / 500000000) (162987 / 1000000000) (Real.log (1000163 / 1000000)) := by
  have h := reflection_log_1779_neg
  have he : Real.log (1000163 / 1000000) = -Real.log (1000000 / 1000163) := by
    rw [show ((1000163 / 1000000) : ℝ) = ((1000000 / 1000163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1780_neg : (163013 / 1000000000) ≤ -Real.log (999837 / 1000000) ∧
    -Real.log (999837 / 1000000) ≤ (81507 / 500000000) := by
  have h := checkLog_sound (w := (163 / 1999837)) (n := 12)
    (lo := (163013 / 1000000000)) (hi := (81507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999837) = 1/(999837 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1780 : Bounds (-81507 / 500000000) (-163013 / 1000000000) (Real.log (999837 / 1000000)) := by
  have h := reflection_log_1780_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1781_neg : (19647567 / 250000000) ≤ -Real.log (1000000 / 1081761) ∧
    -Real.log (1000000 / 1081761) ≤ (78590269 / 1000000000) := by
  have h := checkLog_sound (w := (81761 / 2081761)) (n := 12)
    (lo := (19647567 / 250000000)) (hi := (78590269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081761 / 1000000) = 1/(1000000 / 1081761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1781 : Bounds (19647567 / 250000000) (78590269 / 1000000000) (Real.log (1081761 / 1000000)) := by
  have h := reflection_log_1781_neg
  have he : Real.log (1081761 / 1000000) = -Real.log (1000000 / 1081761) := by
    rw [show ((1081761 / 1000000) : ℝ) = ((1000000 / 1081761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1782_neg : (85297573 / 1000000000) ≤ -Real.log (918239 / 1000000) ∧
    -Real.log (918239 / 1000000) ≤ (42648787 / 500000000) := by
  have h := checkLog_sound (w := (81761 / 1918239)) (n := 12)
    (lo := (85297573 / 1000000000)) (hi := (42648787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918239) = 1/(918239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1782 : Bounds (-42648787 / 500000000) (-85297573 / 1000000000) (Real.log (918239 / 1000000)) := by
  have h := reflection_log_1782_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1783_neg : (39394037 / 500000000) ≤ -Real.log (40000 / 43279) ∧
    -Real.log (40000 / 43279) ≤ (3151523 / 40000000) := by
  have h := checkLog_sound (w := (3279 / 83279)) (n := 12)
    (lo := (39394037 / 500000000)) (hi := (3151523 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43279 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43279 / 40000) = 1/(40000 / 43279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1783 : Bounds (39394037 / 500000000) (3151523 / 40000000) (Real.log (43279 / 40000)) := by
  have h := reflection_log_1783_neg
  have he : Real.log (43279 / 40000) = -Real.log (40000 / 43279) := by
    rw [show ((43279 / 40000) : ℝ) = ((40000 / 43279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1784_neg : (17106131 / 200000000) ≤ -Real.log (36721 / 40000) ∧
    -Real.log (36721 / 40000) ≤ (2672833 / 31250000) := by
  have h := checkLog_sound (w := (3279 / 76721)) (n := 12)
    (lo := (17106131 / 200000000)) (hi := (2672833 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36721) = 1/(36721 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1784 : Bounds (-2672833 / 31250000) (-17106131 / 200000000) (Real.log (36721 / 40000)) := by
  have h := reflection_log_1784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1785_neg : (337129 / 50000000) ≤ -Real.log (1589248159 / 1600000000) ∧
    -Real.log (1589248159 / 1600000000) ≤ (6742581 / 1000000000) := by
  have h := checkLog_sound (w := (10751841 / 3189248159)) (n := 12)
    (lo := (337129 / 50000000)) (hi := (6742581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1589248159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1589248159) = 1/(1589248159 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1785 : Bounds (-6742581 / 1000000000) (-337129 / 50000000) (Real.log (1589248159 / 1600000000)) := by
  have h := reflection_log_1785_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1786_neg : (838413 / 125000000) ≤ -Real.log (993315138879 / 1000000000000) ∧
    -Real.log (993315138879 / 1000000000000) ≤ (1341461 / 200000000) := by
  have h := checkLog_sound (w := (6684861121 / 1993315138879)) (n := 12)
    (lo := (838413 / 125000000)) (hi := (1341461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993315138879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993315138879) = 1/(993315138879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1786 : Bounds (-1341461 / 200000000) (-838413 / 125000000) (Real.log (993315138879 / 1000000000000)) := by
  have h := reflection_log_1786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1787_neg : (81943921 / 500000000) ≤ -Real.log (500000000000 / 589041088431) ∧
    -Real.log (500000000000 / 589041088431) ≤ (163887843 / 1000000000) := by
  have h := checkLog_sound (w := (89041088431 / 1089041088431)) (n := 12)
    (lo := (81943921 / 500000000)) (hi := (163887843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589041088431 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589041088431 / 500000000000) = 1/(500000000000 / 589041088431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1787 : Bounds (81943921 / 500000000) (163887843 / 1000000000) (Real.log (589041088431 / 500000000000)) := by
  have h := reflection_log_1787_neg
  have he : Real.log (589041088431 / 500000000000) = -Real.log (500000000000 / 589041088431) := by
    rw [show ((589041088431 / 500000000000) : ℝ) = ((500000000000 / 589041088431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1788_neg : (16431873 / 100000000) ≤ -Real.log (250000000000 / 294647476921) ∧
    -Real.log (250000000000 / 294647476921) ≤ (164318731 / 1000000000) := by
  have h := checkLog_sound (w := (44647476921 / 544647476921)) (n := 12)
    (lo := (16431873 / 100000000)) (hi := (164318731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294647476921 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294647476921 / 250000000000) = 1/(250000000000 / 294647476921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1788 : Bounds (16431873 / 100000000) (164318731 / 1000000000) (Real.log (294647476921 / 250000000000)) := by
  have h := reflection_log_1788_neg
  have he : Real.log (294647476921 / 250000000000) = -Real.log (250000000000 / 294647476921) := by
    rw [show ((294647476921 / 250000000000) : ℝ) = ((250000000000 / 294647476921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1789_neg : (164364313 / 500000000) ≤ -Real.log (125000000000 / 173650101541) ∧
    -Real.log (125000000000 / 173650101541) ≤ (328728627 / 1000000000) := by
  have h := checkLog_sound (w := (48650101541 / 298650101541)) (n := 12)
    (lo := (164364313 / 500000000)) (hi := (328728627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173650101541 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173650101541 / 125000000000) = 1/(125000000000 / 173650101541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1789 : Bounds (164364313 / 500000000) (328728627 / 1000000000) (Real.log (173650101541 / 125000000000)) := by
  have h := reflection_log_1789_neg
  have he : Real.log (173650101541 / 125000000000) = -Real.log (125000000000 / 173650101541) := by
    rw [show ((173650101541 / 125000000000) : ℝ) = ((125000000000 / 173650101541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1790_neg : (164467041 / 500000000) ≤ -Real.log (125000000000 / 173685782557) ∧
    -Real.log (125000000000 / 173685782557) ≤ (328934083 / 1000000000) := by
  have h := checkLog_sound (w := (48685782557 / 298685782557)) (n := 12)
    (lo := (164467041 / 500000000)) (hi := (328934083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173685782557 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173685782557 / 125000000000) = 1/(125000000000 / 173685782557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1790 : Bounds (164467041 / 500000000) (328934083 / 1000000000) (Real.log (173685782557 / 125000000000)) := by
  have h := reflection_log_1790_neg
  have he : Real.log (173685782557 / 125000000000) = -Real.log (125000000000 / 173685782557) := by
    rw [show ((173685782557 / 125000000000) : ℝ) = ((125000000000 / 173685782557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1791_neg : (75544427 / 500000000) ≤ -Real.log (10000 / 11631) ∧
    -Real.log (10000 / 11631) ≤ (30217771 / 200000000) := by
  have h := checkLog_sound (w := (1631 / 21631)) (n := 12)
    (lo := (75544427 / 500000000)) (hi := (30217771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11631 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11631 / 10000) = 1/(10000 / 11631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1791 : Bounds (75544427 / 500000000) (30217771 / 200000000) (Real.log (11631 / 10000)) := by
  have h := reflection_log_1791_neg
  have he : Real.log (11631 / 10000) = -Real.log (10000 / 11631) := by
    rw [show ((11631 / 10000) : ℝ) = ((10000 / 11631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
