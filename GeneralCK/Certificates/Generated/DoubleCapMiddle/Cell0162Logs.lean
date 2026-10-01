import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0162
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

theorem reflection_log_1_neg : (282591009 / 1000000000) ≤ -Real.log (640 / 849) ∧
    -Real.log (640 / 849) ≤ (28259101 / 100000000) := by
  have h := checkLog_sound (w := (209 / 1489)) (n := 12)
    (lo := (282591009 / 1000000000)) (hi := (28259101 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((849 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(849 / 640) = 1/(640 / 849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (282591009 / 1000000000) (28259101 / 100000000) (Real.log (849 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (849 / 640) = -Real.log (640 / 849) := by
    rw [show ((849 / 640) : ℝ) = ((640 / 849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (197680043 / 500000000) ≤ -Real.log (431 / 640) ∧
    -Real.log (431 / 640) ≤ (395360087 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1071)) (n := 12)
    (lo := (197680043 / 500000000)) (hi := (395360087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 431) = 1/(431 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-395360087 / 1000000000) (-197680043 / 500000000) (Real.log (431 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8817163 / 31250000) ≤ -Real.log (5120 / 6789) ∧
    -Real.log (5120 / 6789) ≤ (282149217 / 1000000000) := by
  have h := checkLog_sound (w := (1669 / 11909)) (n := 12)
    (lo := (8817163 / 31250000)) (hi := (282149217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6789 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6789 / 5120) = 1/(5120 / 6789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8817163 / 31250000) (282149217 / 1000000000) (Real.log (6789 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6789 / 5120) = -Real.log (5120 / 6789) := by
    rw [show ((6789 / 5120) : ℝ) = ((5120 / 6789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (197245197 / 500000000) ≤ -Real.log (3451 / 5120) ∧
    -Real.log (3451 / 5120) ≤ (78898079 / 200000000) := by
  have h := checkLog_sound (w := (1669 / 8571)) (n := 12)
    (lo := (197245197 / 500000000)) (hi := (78898079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3451) = 1/(3451 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-78898079 / 200000000) (-197245197 / 500000000) (Real.log (3451 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (125666859 / 250000000) ≤ -Real.log (320 / 529) ∧
    -Real.log (320 / 529) ≤ (502667437 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 849)) (n := 12)
    (lo := (125666859 / 250000000)) (hi := (502667437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((529 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(529 / 320) = 1/(320 / 529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (125666859 / 250000000) (502667437 / 1000000000) (Real.log (529 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (529 / 320) = -Real.log (320 / 529) := by
    rw [show ((529 / 320) : ℝ) = ((320 / 529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1058790793 / 1000000000) ≤ -Real.log (111 / 320) ∧
    -Real.log (111 / 320) ≤ (211758159 / 200000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 111) = 1/(111 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-211758159 / 200000000) (-1058790793 / 1000000000) (Real.log (111 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (501958299 / 1000000000) ≤ -Real.log (2560 / 4229) ∧
    -Real.log (2560 / 4229) ≤ (5019583 / 10000000) := by
  have h := checkLog_sound (w := (1669 / 6789)) (n := 12)
    (lo := (501958299 / 1000000000)) (hi := (5019583 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4229 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4229 / 2560) = 1/(2560 / 4229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (501958299 / 1000000000) (5019583 / 10000000) (Real.log (4229 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4229 / 2560) = -Real.log (2560 / 4229) := by
    rw [show ((4229 / 2560) : ℝ) = ((2560 / 4229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1055418109 / 1000000000) ≤ -Real.log (891 / 2560) ∧
    -Real.log (891 / 2560) ≤ (1055418111 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 2171)) (n := 12)
    (lo := (362270929 / 1000000000)) (hi := (36227093 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 891) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 891) = 1/(891 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1055418111 / 1000000000) (-1055418109 / 1000000000) (Real.log (891 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (96496657 / 250000000) ≤ -Real.log (200000 / 294213) ∧
    -Real.log (200000 / 294213) ≤ (385986629 / 1000000000) := by
  have h := checkLog_sound (w := (94213 / 494213)) (n := 12)
    (lo := (96496657 / 250000000)) (hi := (385986629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294213 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294213 / 200000) = 1/(200000 / 294213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (96496657 / 250000000) (385986629 / 1000000000) (Real.log (294213 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (294213 / 200000) = -Real.log (200000 / 294213) := by
    rw [show ((294213 / 200000) : ℝ) = ((200000 / 294213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4975701 / 7812500) ≤ -Real.log (105787 / 200000) ∧
    -Real.log (105787 / 200000) ≤ (636889729 / 1000000000) := by
  have h := checkLog_sound (w := (94213 / 305787)) (n := 12)
    (lo := (4975701 / 7812500)) (hi := (636889729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 105787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 105787) = 1/(105787 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-636889729 / 1000000000) (-4975701 / 7812500) (Real.log (105787 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (386593487 / 1000000000) ≤ -Real.log (500000 / 735979) ∧
    -Real.log (500000 / 735979) ≤ (24162093 / 62500000) := by
  have h := checkLog_sound (w := (235979 / 1235979)) (n := 12)
    (lo := (386593487 / 1000000000)) (hi := (24162093 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735979 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735979 / 500000) = 1/(500000 / 735979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (386593487 / 1000000000) (24162093 / 62500000) (Real.log (735979 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (735979 / 500000) = -Real.log (500000 / 735979) := by
    rw [show ((735979 / 500000) : ℝ) = ((500000 / 735979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (159644863 / 250000000) ≤ -Real.log (264021 / 500000) ∧
    -Real.log (264021 / 500000) ≤ (638579453 / 1000000000) := by
  have h := checkLog_sound (w := (235979 / 764021)) (n := 12)
    (lo := (159644863 / 250000000)) (hi := (638579453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 264021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 264021) = 1/(264021 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-638579453 / 1000000000) (-159644863 / 250000000) (Real.log (264021 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (37959129 / 125000000) ≤ -Real.log (500000 / 677413) ∧
    -Real.log (500000 / 677413) ≤ (303673033 / 1000000000) := by
  have h := checkLog_sound (w := (177413 / 1177413)) (n := 12)
    (lo := (37959129 / 125000000)) (hi := (303673033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677413 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677413 / 500000) = 1/(500000 / 677413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (37959129 / 125000000) (303673033 / 1000000000) (Real.log (677413 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (677413 / 500000) = -Real.log (500000 / 677413) := by
    rw [show ((677413 / 500000) : ℝ) = ((500000 / 677413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (438235231 / 1000000000) ≤ -Real.log (322587 / 500000) ∧
    -Real.log (322587 / 500000) ≤ (13694851 / 31250000) := by
  have h := checkLog_sound (w := (177413 / 822587)) (n := 12)
    (lo := (438235231 / 1000000000)) (hi := (13694851 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 322587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 322587) = 1/(322587 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-13694851 / 31250000) (-438235231 / 1000000000) (Real.log (322587 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (304233833 / 1000000000) ≤ -Real.log (500000 / 677793) ∧
    -Real.log (500000 / 677793) ≤ (152116917 / 500000000) := by
  have h := checkLog_sound (w := (177793 / 1177793)) (n := 12)
    (lo := (304233833 / 1000000000)) (hi := (152116917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677793 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677793 / 500000) = 1/(500000 / 677793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (304233833 / 1000000000) (152116917 / 500000000) (Real.log (677793 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (677793 / 500000) = -Real.log (500000 / 677793) := by
    rw [show ((677793 / 500000) : ℝ) = ((500000 / 677793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (219706951 / 500000000) ≤ -Real.log (322207 / 500000) ∧
    -Real.log (322207 / 500000) ≤ (439413903 / 1000000000) := by
  have h := checkLog_sound (w := (177793 / 822207)) (n := 12)
    (lo := (219706951 / 500000000)) (hi := (439413903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 322207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 322207) = 1/(322207 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-439413903 / 1000000000) (-219706951 / 500000000) (Real.log (322207 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (204575271 / 200000000) ≤ -Real.log (500000000000 / 1390591471541) ∧
    -Real.log (500000000000 / 1390591471541) ≤ (1022876357 / 1000000000) := by
  have h := checkLog_sound (w := (390591471541 / 2390591471541)) (n := 12)
    (lo := (13189167 / 40000000)) (hi := (41216147 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1390591471541 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1390591471541 / 1000000000000) = 1/(500000000000 / 1390591471541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (204575271 / 200000000) (1022876357 / 1000000000) (Real.log (1390591471541 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1390591471541 / 500000000000) = -Real.log (500000000000 / 1390591471541) := by
    rw [show ((1390591471541 / 500000000000) : ℝ) = ((500000000000 / 1390591471541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1025172939 / 1000000000) ≤ -Real.log (500000000000 / 1393788751653) ∧
    -Real.log (500000000000 / 1393788751653) ≤ (1025172941 / 1000000000) := by
  have h := checkLog_sound (w := (393788751653 / 2393788751653)) (n := 12)
    (lo := (332025759 / 1000000000)) (hi := (2075161 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1393788751653 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1393788751653 / 1000000000000) = 1/(500000000000 / 1393788751653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1025172939 / 1000000000) (1025172941 / 1000000000) (Real.log (1393788751653 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1393788751653 / 500000000000) = -Real.log (500000000000 / 1393788751653) := by
    rw [show ((1393788751653 / 500000000000) : ℝ) = ((500000000000 / 1393788751653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (741908263 / 1000000000) ≤ -Real.log (500000000000 / 1049969465601) ∧
    -Real.log (500000000000 / 1049969465601) ≤ (148381653 / 200000000) := by
  have h := checkLog_sound (w := (49969465601 / 2049969465601)) (n := 12)
    (lo := (48761083 / 1000000000)) (hi := (12190271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1049969465601 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1049969465601 / 1000000000000) = 1/(500000000000 / 1049969465601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (741908263 / 1000000000) (148381653 / 200000000) (Real.log (1049969465601 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1049969465601 / 500000000000) = -Real.log (500000000000 / 1049969465601) := by
    rw [show ((1049969465601 / 500000000000) : ℝ) = ((500000000000 / 1049969465601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (371823867 / 500000000) ≤ -Real.log (500000000000 / 1051797446983) ∧
    -Real.log (500000000000 / 1051797446983) ≤ (92955967 / 125000000) := by
  have h := checkLog_sound (w := (51797446983 / 2051797446983)) (n := 12)
    (lo := (25250277 / 500000000)) (hi := (10100111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1051797446983 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1051797446983 / 1000000000000) = 1/(500000000000 / 1051797446983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (371823867 / 500000000) (92955967 / 125000000) (Real.log (1051797446983 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1051797446983 / 500000000000) = -Real.log (500000000000 / 1051797446983) := by
    rw [show ((1051797446983 / 500000000000) : ℝ) = ((500000000000 / 1051797446983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0162
