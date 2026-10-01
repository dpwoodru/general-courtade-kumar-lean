import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell101
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (16865513 / 62500000) ≤ -Real.log (2560 / 3353) ∧
    -Real.log (2560 / 3353) ≤ (269848209 / 1000000000) := by
  have h := checkLog_sound (w := (793 / 5913)) (n := 12)
    (lo := (16865513 / 62500000)) (hi := (269848209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3353 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3353 / 2560) = 1/(2560 / 3353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (16865513 / 62500000) (269848209 / 1000000000) (Real.log (3353 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3353 / 2560) = -Real.log (2560 / 3353) := by
    rw [show ((3353 / 2560) : ℝ) = ((2560 / 3353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (74144813 / 200000000) ≤ -Real.log (1767 / 2560) ∧
    -Real.log (1767 / 2560) ≤ (185362033 / 500000000) := by
  have h := checkLog_sound (w := (793 / 4327)) (n := 12)
    (lo := (74144813 / 200000000)) (hi := (185362033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1767) = 1/(1767 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-185362033 / 500000000) (-74144813 / 200000000) (Real.log (1767 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67350187 / 250000000) ≤ -Real.log (5120 / 6703) ∧
    -Real.log (5120 / 6703) ≤ (269400749 / 1000000000) := by
  have h := checkLog_sound (w := (1583 / 11823)) (n := 12)
    (lo := (67350187 / 250000000)) (hi := (269400749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6703 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6703 / 5120) = 1/(5120 / 6703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67350187 / 250000000) (269400749 / 1000000000) (Real.log (6703 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6703 / 5120) = -Real.log (5120 / 6703) := by
    rw [show ((6703 / 5120) : ℝ) = ((5120 / 6703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (46234441 / 125000000) ≤ -Real.log (3537 / 5120) ∧
    -Real.log (3537 / 5120) ≤ (369875529 / 1000000000) := by
  have h := checkLog_sound (w := (1583 / 8657)) (n := 12)
    (lo := (46234441 / 125000000)) (hi := (369875529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3537) = 1/(3537 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-369875529 / 1000000000) (-46234441 / 125000000) (Real.log (3537 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (99232769 / 500000000) ≤ -Real.log (100000 / 121953) ∧
    -Real.log (100000 / 121953) ≤ (198465539 / 1000000000) := by
  have h := checkLog_sound (w := (21953 / 221953)) (n := 12)
    (lo := (99232769 / 500000000)) (hi := (198465539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121953 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121953 / 100000) = 1/(100000 / 121953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (99232769 / 500000000) (198465539 / 1000000000) (Real.log (121953 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (121953 / 100000) = -Real.log (100000 / 121953) := by
    rw [show ((121953 / 100000) : ℝ) = ((100000 / 121953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (7745593 / 31250000) ≤ -Real.log (78047 / 100000) ∧
    -Real.log (78047 / 100000) ≤ (247858977 / 1000000000) := by
  have h := checkLog_sound (w := (21953 / 178047)) (n := 12)
    (lo := (7745593 / 31250000)) (hi := (247858977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 78047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 78047) = 1/(78047 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-247858977 / 1000000000) (-7745593 / 31250000) (Real.log (78047 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (99404937 / 500000000) ≤ -Real.log (20000 / 24399) ∧
    -Real.log (20000 / 24399) ≤ (1590479 / 8000000) := by
  have h := checkLog_sound (w := (4399 / 44399)) (n := 12)
    (lo := (99404937 / 500000000)) (hi := (1590479 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24399 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24399 / 20000) = 1/(20000 / 24399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (99404937 / 500000000) (1590479 / 8000000) (Real.log (24399 / 20000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24399 / 20000) = -Real.log (20000 / 24399) := by
    rw [show ((24399 / 20000) : ℝ) = ((20000 / 24399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (124198629 / 500000000) ≤ -Real.log (15601 / 20000) ∧
    -Real.log (15601 / 20000) ≤ (248397259 / 1000000000) := by
  have h := checkLog_sound (w := (4399 / 35601)) (n := 12)
    (lo := (124198629 / 500000000)) (hi := (248397259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15601) = 1/(15601 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-248397259 / 1000000000) (-124198629 / 500000000) (Real.log (15601 / 20000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36529339 / 250000000) ≤ -Real.log (250000 / 289333) ∧
    -Real.log (250000 / 289333) ≤ (146117357 / 1000000000) := by
  have h := checkLog_sound (w := (39333 / 539333)) (n := 12)
    (lo := (36529339 / 250000000)) (hi := (146117357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289333 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(289333 / 250000) = 1/(250000 / 289333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36529339 / 250000000) (146117357 / 1000000000) (Real.log (289333 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (289333 / 250000) = -Real.log (250000 / 289333) := by
    rw [show ((289333 / 250000) : ℝ) = ((250000 / 289333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (17118223 / 100000000) ≤ -Real.log (210667 / 250000) ∧
    -Real.log (210667 / 250000) ≤ (171182231 / 1000000000) := by
  have h := checkLog_sound (w := (39333 / 460667)) (n := 12)
    (lo := (17118223 / 100000000)) (hi := (171182231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 210667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 210667) = 1/(210667 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-171182231 / 1000000000) (-17118223 / 100000000) (Real.log (210667 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (146385177 / 1000000000) ≤ -Real.log (500000 / 578821) ∧
    -Real.log (500000 / 578821) ≤ (73192589 / 500000000) := by
  have h := checkLog_sound (w := (78821 / 1078821)) (n := 12)
    (lo := (146385177 / 1000000000)) (hi := (73192589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((578821 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(578821 / 500000) = 1/(500000 / 578821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (146385177 / 1000000000) (73192589 / 500000000) (Real.log (578821 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (578821 / 500000) = -Real.log (500000 / 578821) := by
    rw [show ((578821 / 500000) : ℝ) = ((500000 / 578821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (5360943 / 31250000) ≤ -Real.log (421179 / 500000) ∧
    -Real.log (421179 / 500000) ≤ (171550177 / 1000000000) := by
  have h := checkLog_sound (w := (78821 / 921179)) (n := 12)
    (lo := (5360943 / 31250000)) (hi := (171550177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 421179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 421179) = 1/(421179 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-171550177 / 1000000000) (-5360943 / 31250000) (Real.log (421179 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (639276277 / 1000000000) ≤ -Real.log (500000000000 / 947554424653) ∧
    -Real.log (500000000000 / 947554424653) ≤ (319638139 / 500000000) := by
  have h := checkLog_sound (w := (447554424653 / 1447554424653)) (n := 12)
    (lo := (639276277 / 1000000000)) (hi := (319638139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((947554424653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(947554424653 / 500000000000) = 1/(500000000000 / 947554424653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (639276277 / 1000000000) (319638139 / 500000000) (Real.log (947554424653 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (947554424653 / 500000000000) = -Real.log (500000000000 / 947554424653) := by
    rw [show ((947554424653 / 500000000000) : ℝ) = ((500000000000 / 947554424653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (320286137 / 500000000) ≤ -Real.log (125000000000 / 237195812111) ∧
    -Real.log (125000000000 / 237195812111) ≤ (25622891 / 40000000) := by
  have h := checkLog_sound (w := (112195812111 / 362195812111)) (n := 12)
    (lo := (320286137 / 500000000)) (hi := (25622891 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237195812111 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237195812111 / 125000000000) = 1/(125000000000 / 237195812111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (320286137 / 500000000) (25622891 / 40000000) (Real.log (237195812111 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (237195812111 / 125000000000) = -Real.log (125000000000 / 237195812111) := by
    rw [show ((237195812111 / 125000000000) : ℝ) = ((125000000000 / 237195812111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (89264903 / 200000000) ≤ -Real.log (250000000000 / 390639614591) ∧
    -Real.log (250000000000 / 390639614591) ≤ (111581129 / 250000000) := by
  have h := checkLog_sound (w := (140639614591 / 640639614591)) (n := 12)
    (lo := (89264903 / 200000000)) (hi := (111581129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390639614591 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390639614591 / 250000000000) = 1/(250000000000 / 390639614591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (89264903 / 200000000) (111581129 / 250000000) (Real.log (390639614591 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (390639614591 / 250000000000) = -Real.log (250000000000 / 390639614591) := by
    rw [show ((390639614591 / 250000000000) : ℝ) = ((250000000000 / 390639614591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (447207133 / 1000000000) ≤ -Real.log (100000000000 / 156393820909) ∧
    -Real.log (100000000000 / 156393820909) ≤ (223603567 / 500000000) := by
  have h := checkLog_sound (w := (56393820909 / 256393820909)) (n := 12)
    (lo := (447207133 / 1000000000)) (hi := (223603567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156393820909 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156393820909 / 100000000000) = 1/(100000000000 / 156393820909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (447207133 / 1000000000) (223603567 / 500000000) (Real.log (156393820909 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (156393820909 / 100000000000) = -Real.log (100000000000 / 156393820909) := by
    rw [show ((156393820909 / 100000000000) : ℝ) = ((100000000000 / 156393820909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (158649793 / 500000000) ≤ -Real.log (250000000000 / 343353491529) ∧
    -Real.log (250000000000 / 343353491529) ≤ (317299587 / 1000000000) := by
  have h := checkLog_sound (w := (93353491529 / 593353491529)) (n := 12)
    (lo := (158649793 / 500000000)) (hi := (317299587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343353491529 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343353491529 / 250000000000) = 1/(250000000000 / 343353491529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (158649793 / 500000000) (317299587 / 1000000000) (Real.log (343353491529 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (343353491529 / 250000000000) = -Real.log (250000000000 / 343353491529) := by
    rw [show ((343353491529 / 250000000000) : ℝ) = ((250000000000 / 343353491529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (158967677 / 500000000) ≤ -Real.log (100000000000 / 137428741699) ∧
    -Real.log (100000000000 / 137428741699) ≤ (63587071 / 200000000) := by
  have h := checkLog_sound (w := (37428741699 / 237428741699)) (n := 12)
    (lo := (158967677 / 500000000)) (hi := (63587071 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137428741699 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137428741699 / 100000000000) = 1/(100000000000 / 137428741699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (158967677 / 500000000) (63587071 / 200000000) (Real.log (137428741699 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (137428741699 / 100000000000) = -Real.log (100000000000 / 137428741699) := by
    rw [show ((137428741699 / 100000000000) : ℝ) = ((100000000000 / 137428741699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (25164999 / 1000000000) ≤ -Real.log (243787249959 / 250000000000) ∧
    -Real.log (243787249959 / 250000000000) ≤ (5033 / 200000) := by
  have h := checkLog_sound (w := (6212750041 / 493787249959)) (n := 12)
    (lo := (25164999 / 1000000000)) (hi := (5033 / 200000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243787249959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243787249959) = 1/(243787249959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5033 / 200000) (-25164999 / 1000000000) (Real.log (243787249959 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (12532437 / 500000000) ≤ -Real.log (60952915111 / 62500000000) ∧
    -Real.log (60952915111 / 62500000000) ≤ (200519 / 8000000) := by
  have h := checkLog_sound (w := (1547084889 / 123452915111)) (n := 12)
    (lo := (12532437 / 500000000)) (hi := (200519 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60952915111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60952915111) = 1/(60952915111 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-200519 / 8000000) (-12532437 / 500000000) (Real.log (60952915111 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell101
