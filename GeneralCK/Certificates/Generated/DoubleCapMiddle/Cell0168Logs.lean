import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0168
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

theorem reflection_log_1_neg : (55987463 / 200000000) ≤ -Real.log (2560 / 3387) ∧
    -Real.log (2560 / 3387) ≤ (69984329 / 250000000) := by
  have h := checkLog_sound (w := (827 / 5947)) (n := 12)
    (lo := (55987463 / 200000000)) (hi := (69984329 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3387 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3387 / 2560) = 1/(2560 / 3387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (55987463 / 200000000) (69984329 / 250000000) (Real.log (3387 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3387 / 2560) = -Real.log (2560 / 3387) := by
    rw [show ((3387 / 2560) : ℝ) = ((2560 / 3387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (390153247 / 1000000000) ≤ -Real.log (1733 / 2560) ∧
    -Real.log (1733 / 2560) ≤ (12192289 / 31250000) := by
  have h := checkLog_sound (w := (827 / 4293)) (n := 12)
    (lo := (390153247 / 1000000000)) (hi := (12192289 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1733) = 1/(1733 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12192289 / 31250000) (-390153247 / 1000000000) (Real.log (1733 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (279494347 / 1000000000) ≤ -Real.log (5120 / 6771) ∧
    -Real.log (5120 / 6771) ≤ (69873587 / 250000000) := by
  have h := checkLog_sound (w := (1651 / 11891)) (n := 12)
    (lo := (279494347 / 1000000000)) (hi := (69873587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6771 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6771 / 5120) = 1/(5120 / 6771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (279494347 / 1000000000) (69873587 / 250000000) (Real.log (6771 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6771 / 5120) = -Real.log (5120 / 6771) := by
    rw [show ((6771 / 5120) : ℝ) = ((5120 / 6771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (389288071 / 1000000000) ≤ -Real.log (3469 / 5120) ∧
    -Real.log (3469 / 5120) ≤ (48661009 / 125000000) := by
  have h := checkLog_sound (w := (1651 / 8589)) (n := 12)
    (lo := (389288071 / 1000000000)) (hi := (48661009 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3469) = 1/(3469 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-48661009 / 125000000) (-389288071 / 1000000000) (Real.log (3469 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (7787579 / 15625000) ≤ -Real.log (1280 / 2107) ∧
    -Real.log (1280 / 2107) ≤ (498405057 / 1000000000) := by
  have h := checkLog_sound (w := (827 / 3387)) (n := 12)
    (lo := (7787579 / 15625000)) (hi := (498405057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2107 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2107 / 1280) = 1/(1280 / 2107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (7787579 / 15625000) (498405057 / 1000000000) (Real.log (2107 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2107 / 1280) = -Real.log (1280 / 2107) := by
    rw [show ((2107 / 1280) : ℝ) = ((1280 / 2107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (103872323 / 100000000) ≤ -Real.log (453 / 1280) ∧
    -Real.log (453 / 1280) ≤ (32460101 / 31250000) := by
  have h := checkLog_sound (w := (187 / 1093)) (n := 12)
    (lo := (6911521 / 20000000)) (hi := (345576051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 453) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 453) = 1/(453 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-32460101 / 31250000) (-103872323 / 100000000) (Real.log (453 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (49769289 / 100000000) ≤ -Real.log (2560 / 4211) ∧
    -Real.log (2560 / 4211) ≤ (497692891 / 1000000000) := by
  have h := checkLog_sound (w := (1651 / 6771)) (n := 12)
    (lo := (49769289 / 100000000)) (hi := (497692891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4211 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4211 / 2560) = 1/(2560 / 4211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (49769289 / 100000000) (497692891 / 1000000000) (Real.log (4211 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4211 / 2560) = -Real.log (2560 / 4211) := by
    rw [show ((4211 / 2560) : ℝ) = ((2560 / 4211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (517708721 / 500000000) ≤ -Real.log (909 / 2560) ∧
    -Real.log (909 / 2560) ≤ (258854361 / 250000000) := by
  have h := checkLog_sound (w := (371 / 2189)) (n := 12)
    (lo := (171135131 / 500000000)) (hi := (342270263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 909) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 909) = 1/(909 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-258854361 / 250000000) (-517708721 / 500000000) (Real.log (909 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (47793153 / 125000000) ≤ -Real.log (500000 / 732859) ∧
    -Real.log (500000 / 732859) ≤ (15293809 / 40000000) := by
  have h := checkLog_sound (w := (232859 / 1232859)) (n := 12)
    (lo := (47793153 / 125000000)) (hi := (15293809 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732859 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732859 / 500000) = 1/(500000 / 732859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (47793153 / 125000000) (15293809 / 40000000) (Real.log (732859 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (732859 / 500000) = -Real.log (500000 / 732859) := by
    rw [show ((732859 / 500000) : ℝ) = ((500000 / 732859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (626831489 / 1000000000) ≤ -Real.log (267141 / 500000) ∧
    -Real.log (267141 / 500000) ≤ (62683149 / 100000000) := by
  have h := checkLog_sound (w := (232859 / 767141)) (n := 12)
    (lo := (626831489 / 1000000000)) (hi := (62683149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 267141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 267141) = 1/(267141 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-62683149 / 100000000) (-626831489 / 1000000000) (Real.log (267141 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (382952933 / 1000000000) ≤ -Real.log (1000000 / 1466609) ∧
    -Real.log (1000000 / 1466609) ≤ (191476467 / 500000000) := by
  have h := checkLog_sound (w := (466609 / 2466609)) (n := 12)
    (lo := (382952933 / 1000000000)) (hi := (191476467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1466609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1466609 / 1000000) = 1/(1000000 / 1466609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (382952933 / 1000000000) (191476467 / 500000000) (Real.log (1466609 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1466609 / 1000000) = -Real.log (1000000 / 1466609) := by
    rw [show ((1466609 / 1000000) : ℝ) = ((1000000 / 1466609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (31425027 / 50000000) ≤ -Real.log (533391 / 1000000) ∧
    -Real.log (533391 / 1000000) ≤ (628500541 / 1000000000) := by
  have h := checkLog_sound (w := (466609 / 1533391)) (n := 12)
    (lo := (31425027 / 50000000)) (hi := (628500541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 533391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 533391) = 1/(533391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-628500541 / 1000000000) (-31425027 / 50000000) (Real.log (533391 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (300316421 / 1000000000) ≤ -Real.log (500000 / 675143) ∧
    -Real.log (500000 / 675143) ≤ (150158211 / 500000000) := by
  have h := checkLog_sound (w := (175143 / 1175143)) (n := 12)
    (lo := (300316421 / 1000000000)) (hi := (150158211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675143 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675143 / 500000) = 1/(500000 / 675143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (300316421 / 1000000000) (150158211 / 500000000) (Real.log (675143 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (675143 / 500000) = -Real.log (500000 / 675143) := by
    rw [show ((675143 / 500000) : ℝ) = ((500000 / 675143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (107805753 / 250000000) ≤ -Real.log (324857 / 500000) ∧
    -Real.log (324857 / 500000) ≤ (431223013 / 1000000000) := by
  have h := checkLog_sound (w := (175143 / 824857)) (n := 12)
    (lo := (107805753 / 250000000)) (hi := (431223013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 324857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 324857) = 1/(324857 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-431223013 / 1000000000) (-107805753 / 250000000) (Real.log (324857 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (150437703 / 500000000) ≤ -Real.log (1000000 / 1351041) ∧
    -Real.log (1000000 / 1351041) ≤ (300875407 / 1000000000) := by
  have h := checkLog_sound (w := (351041 / 2351041)) (n := 12)
    (lo := (150437703 / 500000000)) (hi := (300875407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1351041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1351041 / 1000000) = 1/(1000000 / 1351041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (150437703 / 500000000) (300875407 / 1000000000) (Real.log (1351041 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1351041 / 1000000) = -Real.log (1000000 / 1351041) := by
    rw [show ((1351041 / 1000000) : ℝ) = ((1000000 / 1351041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (216192869 / 500000000) ≤ -Real.log (648959 / 1000000) ∧
    -Real.log (648959 / 1000000) ≤ (432385739 / 1000000000) := by
  have h := checkLog_sound (w := (351041 / 1648959)) (n := 12)
    (lo := (216192869 / 500000000)) (hi := (432385739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 648959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 648959) = 1/(648959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-432385739 / 1000000000) (-216192869 / 500000000) (Real.log (648959 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1009176713 / 1000000000) ≤ -Real.log (32000000 / 87786929) ∧
    -Real.log (32000000 / 87786929) ≤ (201835343 / 200000000) := by
  have h := checkLog_sound (w := (23786929 / 151786929)) (n := 12)
    (lo := (316029533 / 1000000000)) (hi := (158014767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87786929 / 64000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(87786929 / 64000000) = 1/(32000000 / 87786929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1009176713 / 1000000000) (201835343 / 200000000) (Real.log (87786929 / 32000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (87786929 / 32000000) = -Real.log (32000000 / 87786929) := by
    rw [show ((87786929 / 32000000) : ℝ) = ((32000000 / 87786929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1011453473 / 1000000000) ≤ -Real.log (62500000000 / 171849660943) ∧
    -Real.log (62500000000 / 171849660943) ≤ (40458139 / 40000000) := by
  have h := checkLog_sound (w := (46849660943 / 296849660943)) (n := 12)
    (lo := (318306293 / 1000000000)) (hi := (159153147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171849660943 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(171849660943 / 125000000000) = 1/(62500000000 / 171849660943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1011453473 / 1000000000) (40458139 / 40000000) (Real.log (171849660943 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (171849660943 / 62500000000) = -Real.log (62500000000 / 171849660943) := by
    rw [show ((171849660943 / 62500000000) : ℝ) = ((62500000000 / 171849660943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (365769717 / 500000000) ≤ -Real.log (100000000000 / 207827751903) ∧
    -Real.log (100000000000 / 207827751903) ≤ (182884859 / 250000000) := by
  have h := checkLog_sound (w := (7827751903 / 407827751903)) (n := 12)
    (lo := (19196127 / 500000000)) (hi := (7678451 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207827751903 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(207827751903 / 200000000000) = 1/(100000000000 / 207827751903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (365769717 / 500000000) (182884859 / 250000000) (Real.log (207827751903 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (207827751903 / 100000000000) = -Real.log (100000000000 / 207827751903) := by
    rw [show ((207827751903 / 100000000000) : ℝ) = ((100000000000 / 207827751903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (91657643 / 125000000) ≤ -Real.log (125000000000 / 260232349039) ∧
    -Real.log (125000000000 / 260232349039) ≤ (366630573 / 500000000) := by
  have h := checkLog_sound (w := (10232349039 / 510232349039)) (n := 12)
    (lo := (10028491 / 250000000)) (hi := (8022793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((260232349039 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(260232349039 / 250000000000) = 1/(125000000000 / 260232349039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (91657643 / 125000000) (366630573 / 500000000) (Real.log (260232349039 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (260232349039 / 125000000000) = -Real.log (125000000000 / 260232349039) := by
    rw [show ((260232349039 / 125000000000) : ℝ) = ((125000000000 / 260232349039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0168
