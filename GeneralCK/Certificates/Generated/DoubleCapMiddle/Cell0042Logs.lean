import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0042
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

theorem reflection_log_1_neg : (380948261 / 1000000000) ≤ -Real.log (2560 / 3747) ∧
    -Real.log (2560 / 3747) ≤ (190474131 / 500000000) := by
  have h := checkLog_sound (w := (1187 / 6307)) (n := 12)
    (lo := (380948261 / 1000000000)) (hi := (190474131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3747 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3747 / 2560) = 1/(2560 / 3747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (380948261 / 1000000000) (190474131 / 500000000) (Real.log (3747 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3747 / 2560) = -Real.log (2560 / 3747) := by
    rw [show ((3747 / 2560) : ℝ) = ((2560 / 3747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (623009131 / 1000000000) ≤ -Real.log (1373 / 2560) ∧
    -Real.log (1373 / 2560) ≤ (155752283 / 250000000) := by
  have h := checkLog_sound (w := (1187 / 3933)) (n := 12)
    (lo := (623009131 / 1000000000)) (hi := (155752283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1373) = 1/(1373 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-155752283 / 250000000) (-623009131 / 1000000000) (Real.log (1373 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (3801473 / 10000000) ≤ -Real.log (80 / 117) ∧
    -Real.log (80 / 117) ≤ (380147301 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 197)) (n := 12)
    (lo := (3801473 / 10000000)) (hi := (380147301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117 / 80) = 1/(80 / 117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (3801473 / 10000000) (380147301 / 1000000000) (Real.log (117 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (117 / 80) = -Real.log (80 / 117) := by
    rw [show ((117 / 80) : ℝ) = ((80 / 117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (310413259 / 500000000) ≤ -Real.log (43 / 80) ∧
    -Real.log (43 / 80) ≤ (620826519 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 123)) (n := 12)
    (lo := (310413259 / 500000000)) (hi := (620826519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 43) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 43) = 1/(43 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-620826519 / 1000000000) (-310413259 / 500000000) (Real.log (43 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (656142759 / 1000000000) ≤ -Real.log (1280 / 2467) ∧
    -Real.log (1280 / 2467) ≤ (16403569 / 25000000) := by
  have h := checkLog_sound (w := (1187 / 3747)) (n := 12)
    (lo := (656142759 / 1000000000)) (hi := (16403569 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2467 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2467 / 1280) = 1/(1280 / 2467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (656142759 / 1000000000) (16403569 / 25000000) (Real.log (2467 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2467 / 1280) = -Real.log (1280 / 2467) := by
    rw [show ((2467 / 1280) : ℝ) = ((1280 / 2467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1311007931 / 500000000) ≤ -Real.log (93 / 1280) ∧
    -Real.log (93 / 1280) ≤ (1311007933 / 500000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 93) = 1/(93 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1311007933 / 500000000) (-1311007931 / 500000000) (Real.log (93 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (654925967 / 1000000000) ≤ -Real.log (40 / 77) ∧
    -Real.log (40 / 77) ≤ (40932873 / 62500000) := by
  have h := checkLog_sound (w := (37 / 117)) (n := 12)
    (lo := (654925967 / 1000000000)) (hi := (40932873 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77 / 40) = 1/(40 / 77) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (654925967 / 1000000000) (40932873 / 62500000) (Real.log (77 / 40)) := by
  have h := reflection_log_7_neg
  have he : Real.log (77 / 40) = -Real.log (40 / 77) := by
    rw [show ((77 / 40) : ℝ) = ((40 / 77) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2590267163 / 1000000000) ≤ -Real.log (3 / 40) ∧
    -Real.log (3 / 40) ≤ (2590267167 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5 / 3) = 1/(3 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2590267167 / 1000000000) (-2590267163 / 1000000000) (Real.log (3 / 40)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (528018967 / 1000000000) ≤ -Real.log (100000 / 169557) ∧
    -Real.log (100000 / 169557) ≤ (66002371 / 125000000) := by
  have h := checkLog_sound (w := (69557 / 269557)) (n := 12)
    (lo := (528018967 / 1000000000)) (hi := (66002371 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169557 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169557 / 100000) = 1/(100000 / 169557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (528018967 / 1000000000) (66002371 / 125000000) (Real.log (169557 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (169557 / 100000) = -Real.log (100000 / 169557) := by
    rw [show ((169557 / 100000) : ℝ) = ((100000 / 169557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (594657051 / 500000000) ≤ -Real.log (30443 / 100000) ∧
    -Real.log (30443 / 100000) ≤ (148664263 / 125000000) := by
  have h := checkLog_sound (w := (19557 / 80443)) (n := 12)
    (lo := (248083461 / 500000000)) (hi := (496166923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 30443) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 30443) = 1/(30443 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-148664263 / 125000000) (-594657051 / 500000000) (Real.log (30443 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (264663997 / 500000000) ≤ -Real.log (1000000 / 1697791) ∧
    -Real.log (1000000 / 1697791) ≤ (105865599 / 200000000) := by
  have h := checkLog_sound (w := (697791 / 2697791)) (n := 12)
    (lo := (264663997 / 500000000)) (hi := (105865599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1697791 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1697791 / 1000000) = 1/(1000000 / 1697791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (264663997 / 500000000) (105865599 / 200000000) (Real.log (1697791 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1697791 / 1000000) = -Real.log (1000000 / 1697791) := by
    rw [show ((1697791 / 1000000) : ℝ) = ((1000000 / 1697791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1196636447 / 1000000000) ≤ -Real.log (302209 / 1000000) ∧
    -Real.log (302209 / 1000000) ≤ (1196636449 / 1000000000) := by
  have h := checkLog_sound (w := (197791 / 802209)) (n := 12)
    (lo := (503489267 / 1000000000)) (hi := (125872317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 302209) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 302209) = 1/(302209 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1196636449 / 1000000000) (-1196636447 / 1000000000) (Real.log (302209 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (448974049 / 1000000000) ≤ -Real.log (62500 / 97919) ∧
    -Real.log (62500 / 97919) ≤ (8979481 / 20000000) := by
  have h := checkLog_sound (w := (35419 / 160419)) (n := 12)
    (lo := (448974049 / 1000000000)) (hi := (8979481 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97919 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97919 / 62500) = 1/(62500 / 97919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (448974049 / 1000000000) (8979481 / 20000000) (Real.log (97919 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (97919 / 62500) = -Real.log (62500 / 97919) := by
    rw [show ((97919 / 62500) : ℝ) = ((62500 / 97919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (836334181 / 1000000000) ≤ -Real.log (27081 / 62500) ∧
    -Real.log (27081 / 62500) ≤ (836334183 / 1000000000) := by
  have h := checkLog_sound (w := (4169 / 58331)) (n := 12)
    (lo := (143187001 / 1000000000)) (hi := (71593501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27081) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 27081) = 1/(27081 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-836334183 / 1000000000) (-836334181 / 1000000000) (Real.log (27081 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (450469703 / 1000000000) ≤ -Real.log (1000000 / 1569049) ∧
    -Real.log (1000000 / 1569049) ≤ (56308713 / 125000000) := by
  have h := checkLog_sound (w := (569049 / 2569049)) (n := 12)
    (lo := (450469703 / 1000000000)) (hi := (56308713 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1569049 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1569049 / 1000000) = 1/(1000000 / 1569049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (450469703 / 1000000000) (56308713 / 125000000) (Real.log (1569049 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1569049 / 1000000) = -Real.log (1000000 / 1569049) := by
    rw [show ((1569049 / 1000000) : ℝ) = ((1000000 / 1569049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (841760883 / 1000000000) ≤ -Real.log (430951 / 1000000) ∧
    -Real.log (430951 / 1000000) ≤ (168352177 / 200000000) := by
  have h := checkLog_sound (w := (69049 / 930951)) (n := 12)
    (lo := (148613703 / 1000000000)) (hi := (18576713 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 430951) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 430951) = 1/(430951 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-168352177 / 200000000) (-841760883 / 1000000000) (Real.log (430951 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1717333069 / 1000000000) ≤ -Real.log (500000000000 / 2784827382321) ∧
    -Real.log (500000000000 / 2784827382321) ≤ (107333317 / 62500000) := by
  have h := checkLog_sound (w := (784827382321 / 4784827382321)) (n := 12)
    (lo := (331038709 / 1000000000)) (hi := (33103871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2784827382321 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2784827382321 / 2000000000000) = 1/(500000000000 / 2784827382321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1717333069 / 1000000000) (107333317 / 62500000) (Real.log (2784827382321 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2784827382321 / 500000000000) = -Real.log (500000000000 / 2784827382321) := by
    rw [show ((2784827382321 / 500000000000) : ℝ) = ((500000000000 / 2784827382321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1725964441 / 1000000000) ≤ -Real.log (20000000000 / 112358731871) ∧
    -Real.log (20000000000 / 112358731871) ≤ (431491111 / 250000000) := by
  have h := checkLog_sound (w := (32358731871 / 192358731871)) (n := 12)
    (lo := (339670081 / 1000000000)) (hi := (169835041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112358731871 / 80000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(112358731871 / 80000000000) = 1/(20000000000 / 112358731871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1725964441 / 1000000000) (431491111 / 250000000) (Real.log (112358731871 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (112358731871 / 20000000000) = -Real.log (20000000000 / 112358731871) := by
    rw [show ((112358731871 / 20000000000) : ℝ) = ((20000000000 / 112358731871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (128530823 / 100000000) ≤ -Real.log (50000000000 / 180789114139) ∧
    -Real.log (50000000000 / 180789114139) ≤ (160663529 / 125000000) := by
  have h := checkLog_sound (w := (80789114139 / 280789114139)) (n := 12)
    (lo := (11843221 / 20000000)) (hi := (592161051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180789114139 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(180789114139 / 100000000000) = 1/(50000000000 / 180789114139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (128530823 / 100000000) (160663529 / 125000000) (Real.log (180789114139 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (180789114139 / 50000000000) = -Real.log (50000000000 / 180789114139) := by
    rw [show ((180789114139 / 50000000000) : ℝ) = ((50000000000 / 180789114139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1292230587 / 1000000000) ≤ -Real.log (100000000000 / 364089884929) ∧
    -Real.log (100000000000 / 364089884929) ≤ (1292230589 / 1000000000) := by
  have h := checkLog_sound (w := (164089884929 / 564089884929)) (n := 12)
    (lo := (599083407 / 1000000000)) (hi := (37442713 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364089884929 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(364089884929 / 200000000000) = 1/(100000000000 / 364089884929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1292230587 / 1000000000) (1292230589 / 1000000000) (Real.log (364089884929 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (364089884929 / 100000000000) = -Real.log (100000000000 / 364089884929) := by
    rw [show ((364089884929 / 100000000000) : ℝ) = ((100000000000 / 364089884929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0042
