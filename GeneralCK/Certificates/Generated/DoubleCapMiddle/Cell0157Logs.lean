import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0157
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

theorem reflection_log_1_neg : (56959411 / 200000000) ≤ -Real.log (5120 / 6807) ∧
    -Real.log (5120 / 6807) ≤ (2224977 / 7812500) := by
  have h := checkLog_sound (w := (1687 / 11927)) (n := 12)
    (lo := (56959411 / 200000000)) (hi := (2224977 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6807 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6807 / 5120) = 1/(5120 / 6807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (56959411 / 200000000) (2224977 / 7812500) (Real.log (6807 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6807 / 5120) = -Real.log (5120 / 6807) := by
    rw [show ((6807 / 5120) : ℝ) = ((5120 / 6807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (99929981 / 250000000) ≤ -Real.log (3433 / 5120) ∧
    -Real.log (3433 / 5120) ≤ (15988797 / 40000000) := by
  have h := checkLog_sound (w := (1687 / 8553)) (n := 12)
    (lo := (99929981 / 250000000)) (hi := (15988797 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3433) = 1/(3433 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-15988797 / 40000000) (-99929981 / 250000000) (Real.log (3433 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (56871247 / 200000000) ≤ -Real.log (1280 / 1701) ∧
    -Real.log (1280 / 1701) ≤ (71089059 / 250000000) := by
  have h := checkLog_sound (w := (421 / 2981)) (n := 12)
    (lo := (56871247 / 200000000)) (hi := (71089059 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1701 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1701 / 1280) = 1/(1280 / 1701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (56871247 / 200000000) (71089059 / 250000000) (Real.log (1701 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1701 / 1280) = -Real.log (1280 / 1701) := by
    rw [show ((1701 / 1280) : ℝ) = ((1280 / 1701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (199423217 / 500000000) ≤ -Real.log (859 / 1280) ∧
    -Real.log (859 / 1280) ≤ (79769287 / 200000000) := by
  have h := checkLog_sound (w := (421 / 2139)) (n := 12)
    (lo := (199423217 / 500000000)) (hi := (79769287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 859) = 1/(859 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-79769287 / 200000000) (-199423217 / 500000000) (Real.log (859 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (63275699 / 125000000) ≤ -Real.log (2560 / 4247) ∧
    -Real.log (2560 / 4247) ≤ (506205593 / 1000000000) := by
  have h := checkLog_sound (w := (1687 / 6807)) (n := 12)
    (lo := (63275699 / 125000000)) (hi := (506205593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4247 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4247 / 2560) = 1/(2560 / 4247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (63275699 / 125000000) (506205593 / 1000000000) (Real.log (4247 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4247 / 2560) = -Real.log (2560 / 4247) := by
    rw [show ((4247 / 2560) : ℝ) = ((2560 / 4247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1075826981 / 1000000000) ≤ -Real.log (873 / 2560) ∧
    -Real.log (873 / 2560) ≤ (1075826983 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 2153)) (n := 12)
    (lo := (382679801 / 1000000000)) (hi := (191339901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 873) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 873) = 1/(873 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1075826983 / 1000000000) (-1075826981 / 1000000000) (Real.log (873 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (252749481 / 500000000) ≤ -Real.log (640 / 1061) ∧
    -Real.log (640 / 1061) ≤ (505498963 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 1701)) (n := 12)
    (lo := (252749481 / 500000000)) (hi := (505498963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1061 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1061 / 640) = 1/(640 / 1061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (252749481 / 500000000) (505498963 / 1000000000) (Real.log (1061 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1061 / 640) = -Real.log (640 / 1061) := by
    rw [show ((1061 / 640) : ℝ) = ((640 / 1061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (214479289 / 200000000) ≤ -Real.log (219 / 640) ∧
    -Real.log (219 / 640) ≤ (1072396447 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 539)) (n := 12)
    (lo := (75849853 / 200000000)) (hi := (189624633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 219) = 1/(219 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1072396447 / 1000000000) (-214479289 / 200000000) (Real.log (219 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (389016569 / 1000000000) ≤ -Real.log (1000000 / 1475529) ∧
    -Real.log (1000000 / 1475529) ≤ (38901657 / 100000000) := by
  have h := checkLog_sound (w := (475529 / 2475529)) (n := 12)
    (lo := (389016569 / 1000000000)) (hi := (38901657 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1475529 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1475529 / 1000000) = 1/(1000000 / 1475529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (389016569 / 1000000000) (38901657 / 100000000) (Real.log (1475529 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1475529 / 1000000) = -Real.log (1000000 / 1475529) := by
    rw [show ((1475529 / 1000000) : ℝ) = ((1000000 / 1475529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (645365143 / 1000000000) ≤ -Real.log (524471 / 1000000) ∧
    -Real.log (524471 / 1000000) ≤ (80670643 / 125000000) := by
  have h := checkLog_sound (w := (475529 / 1524471)) (n := 12)
    (lo := (645365143 / 1000000000)) (hi := (80670643 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 524471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 524471) = 1/(524471 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-80670643 / 125000000) (-645365143 / 1000000000) (Real.log (524471 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (389622947 / 1000000000) ≤ -Real.log (125000 / 184553) ∧
    -Real.log (125000 / 184553) ≤ (97405737 / 250000000) := by
  have h := checkLog_sound (w := (59553 / 309553)) (n := 12)
    (lo := (389622947 / 1000000000)) (hi := (97405737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184553 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184553 / 125000) = 1/(125000 / 184553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (389622947 / 1000000000) (97405737 / 250000000) (Real.log (184553 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (184553 / 125000) = -Real.log (125000 / 184553) := by
    rw [show ((184553 / 125000) : ℝ) = ((125000 / 184553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (323536541 / 500000000) ≤ -Real.log (65447 / 125000) ∧
    -Real.log (65447 / 125000) ≤ (647073083 / 1000000000) := by
  have h := checkLog_sound (w := (59553 / 190447)) (n := 12)
    (lo := (323536541 / 500000000)) (hi := (647073083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 65447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 65447) = 1/(65447 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-647073083 / 1000000000) (-323536541 / 500000000) (Real.log (65447 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (306478311 / 1000000000) ≤ -Real.log (125000 / 169829) ∧
    -Real.log (125000 / 169829) ≤ (38309789 / 125000000) := by
  have h := checkLog_sound (w := (44829 / 294829)) (n := 12)
    (lo := (306478311 / 1000000000)) (hi := (38309789 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169829 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169829 / 125000) = 1/(125000 / 169829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (306478311 / 1000000000) (38309789 / 125000000) (Real.log (169829 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (169829 / 125000) = -Real.log (125000 / 169829) := by
    rw [show ((169829 / 125000) : ℝ) = ((125000 / 169829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (444151883 / 1000000000) ≤ -Real.log (80171 / 125000) ∧
    -Real.log (80171 / 125000) ≤ (111037971 / 250000000) := by
  have h := checkLog_sound (w := (44829 / 205171)) (n := 12)
    (lo := (444151883 / 1000000000)) (hi := (111037971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 80171) = 1/(80171 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-111037971 / 250000000) (-444151883 / 1000000000) (Real.log (80171 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (307040483 / 1000000000) ≤ -Real.log (250000 / 339849) ∧
    -Real.log (250000 / 339849) ≤ (76760121 / 250000000) := by
  have h := checkLog_sound (w := (89849 / 589849)) (n := 12)
    (lo := (307040483 / 1000000000)) (hi := (76760121 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339849 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339849 / 250000) = 1/(250000 / 339849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (307040483 / 1000000000) (76760121 / 250000000) (Real.log (339849 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (339849 / 250000) = -Real.log (250000 / 339849) := by
    rw [show ((339849 / 250000) : ℝ) = ((250000 / 339849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (445343797 / 1000000000) ≤ -Real.log (160151 / 250000) ∧
    -Real.log (160151 / 250000) ≤ (222671899 / 500000000) := by
  have h := checkLog_sound (w := (89849 / 410151)) (n := 12)
    (lo := (445343797 / 1000000000)) (hi := (222671899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 160151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 160151) = 1/(160151 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-222671899 / 500000000) (-445343797 / 1000000000) (Real.log (160151 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (64648857 / 62500000) ≤ -Real.log (250000000000 / 703341557493) ∧
    -Real.log (250000000000 / 703341557493) ≤ (517190857 / 500000000) := by
  have h := checkLog_sound (w := (203341557493 / 1203341557493)) (n := 12)
    (lo := (85308633 / 250000000)) (hi := (341234533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703341557493 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(703341557493 / 500000000000) = 1/(250000000000 / 703341557493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (64648857 / 62500000) (517190857 / 500000000) (Real.log (703341557493 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (703341557493 / 250000000000) = -Real.log (250000000000 / 703341557493) := by
    rw [show ((703341557493 / 250000000000) : ℝ) = ((250000000000 / 703341557493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1036696029 / 1000000000) ≤ -Real.log (250000000000 / 704971198069) ∧
    -Real.log (250000000000 / 704971198069) ≤ (1036696031 / 1000000000) := by
  have h := checkLog_sound (w := (204971198069 / 1204971198069)) (n := 12)
    (lo := (343548849 / 1000000000)) (hi := (6870977 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704971198069 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(704971198069 / 500000000000) = 1/(250000000000 / 704971198069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1036696029 / 1000000000) (1036696031 / 1000000000) (Real.log (704971198069 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (704971198069 / 250000000000) = -Real.log (250000000000 / 704971198069) := by
    rw [show ((704971198069 / 250000000000) : ℝ) = ((250000000000 / 704971198069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (375315097 / 500000000) ≤ -Real.log (500000000000 / 1059167279939) ∧
    -Real.log (500000000000 / 1059167279939) ≤ (187657549 / 250000000) := by
  have h := checkLog_sound (w := (59167279939 / 2059167279939)) (n := 12)
    (lo := (28741507 / 500000000)) (hi := (11496603 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1059167279939 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1059167279939 / 1000000000000) = 1/(500000000000 / 1059167279939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (375315097 / 500000000) (187657549 / 250000000) (Real.log (1059167279939 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1059167279939 / 500000000000) = -Real.log (500000000000 / 1059167279939) := by
    rw [show ((1059167279939 / 500000000000) : ℝ) = ((500000000000 / 1059167279939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (18809607 / 25000000) ≤ -Real.log (31250000000 / 66314173811) ∧
    -Real.log (31250000000 / 66314173811) ≤ (376192141 / 500000000) := by
  have h := checkLog_sound (w := (3814173811 / 128814173811)) (n := 12)
    (lo := (592371 / 10000000)) (hi := (59237101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66314173811 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(66314173811 / 62500000000) = 1/(31250000000 / 66314173811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (18809607 / 25000000) (376192141 / 500000000) (Real.log (66314173811 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (66314173811 / 31250000000) = -Real.log (31250000000 / 66314173811) := by
    rw [show ((66314173811 / 31250000000) : ℝ) = ((31250000000 / 66314173811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0157
