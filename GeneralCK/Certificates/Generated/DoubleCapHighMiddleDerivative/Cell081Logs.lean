import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell081
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

theorem reflection_log_1_neg : (26086073 / 100000000) ≤ -Real.log (2560 / 3323) ∧
    -Real.log (2560 / 3323) ≤ (260860731 / 1000000000) := by
  have h := checkLog_sound (w := (763 / 5883)) (n := 12)
    (lo := (26086073 / 100000000)) (hi := (260860731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3323 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3323 / 2560) = 1/(2560 / 3323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (26086073 / 100000000) (260860731 / 1000000000) (Real.log (3323 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3323 / 2560) = -Real.log (2560 / 3323) := by
    rw [show ((3323 / 2560) : ℝ) = ((2560 / 3323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (7077773 / 20000000) ≤ -Real.log (1797 / 2560) ∧
    -Real.log (1797 / 2560) ≤ (353888651 / 1000000000) := by
  have h := checkLog_sound (w := (763 / 4357)) (n := 12)
    (lo := (7077773 / 20000000)) (hi := (353888651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1797) = 1/(1797 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-353888651 / 1000000000) (-7077773 / 20000000) (Real.log (1797 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (260409229 / 1000000000) ≤ -Real.log (5120 / 6643) ∧
    -Real.log (5120 / 6643) ≤ (26040923 / 100000000) := by
  have h := checkLog_sound (w := (1523 / 11763)) (n := 12)
    (lo := (260409229 / 1000000000)) (hi := (26040923 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6643 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6643 / 5120) = 1/(5120 / 6643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (260409229 / 1000000000) (26040923 / 100000000) (Real.log (6643 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6643 / 5120) = -Real.log (5120 / 6643) := by
    rw [show ((6643 / 5120) : ℝ) = ((5120 / 6643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (176527137 / 500000000) ≤ -Real.log (3597 / 5120) ∧
    -Real.log (3597 / 5120) ≤ (14122171 / 40000000) := by
  have h := checkLog_sound (w := (1523 / 8717)) (n := 12)
    (lo := (176527137 / 500000000)) (hi := (14122171 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3597) = 1/(3597 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-14122171 / 40000000) (-176527137 / 500000000) (Real.log (3597 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (19156289 / 100000000) ≤ -Real.log (1000000 / 1211141) ∧
    -Real.log (1000000 / 1211141) ≤ (191562891 / 1000000000) := by
  have h := checkLog_sound (w := (211141 / 2211141)) (n := 12)
    (lo := (19156289 / 100000000)) (hi := (191562891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211141 / 1000000) = 1/(1000000 / 1211141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (19156289 / 100000000) (191562891 / 1000000000) (Real.log (1211141 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1211141 / 1000000) = -Real.log (1000000 / 1211141) := by
    rw [show ((1211141 / 1000000) : ℝ) = ((1000000 / 1211141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (237167681 / 1000000000) ≤ -Real.log (788859 / 1000000) ∧
    -Real.log (788859 / 1000000) ≤ (118583841 / 500000000) := by
  have h := checkLog_sound (w := (211141 / 1788859)) (n := 12)
    (lo := (237167681 / 1000000000)) (hi := (118583841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 788859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 788859) = 1/(788859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-118583841 / 500000000) (-237167681 / 1000000000) (Real.log (788859 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (47977609 / 250000000) ≤ -Real.log (500000 / 605781) ∧
    -Real.log (500000 / 605781) ≤ (191910437 / 1000000000) := by
  have h := checkLog_sound (w := (105781 / 1105781)) (n := 12)
    (lo := (47977609 / 250000000)) (hi := (191910437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605781 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605781 / 500000) = 1/(500000 / 605781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (47977609 / 250000000) (191910437 / 1000000000) (Real.log (605781 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (605781 / 500000) = -Real.log (500000 / 605781) := by
    rw [show ((605781 / 500000) : ℝ) = ((500000 / 605781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (47540301 / 200000000) ≤ -Real.log (394219 / 500000) ∧
    -Real.log (394219 / 500000) ≤ (118850753 / 500000000) := by
  have h := checkLog_sound (w := (105781 / 894219)) (n := 12)
    (lo := (47540301 / 200000000)) (hi := (118850753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 394219) = 1/(394219 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-118850753 / 500000000) (-47540301 / 200000000) (Real.log (394219 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (14077621 / 100000000) ≤ -Real.log (1000000 / 1151167) ∧
    -Real.log (1000000 / 1151167) ≤ (140776211 / 1000000000) := by
  have h := checkLog_sound (w := (151167 / 2151167)) (n := 12)
    (lo := (14077621 / 100000000)) (hi := (140776211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1151167 / 1000000) = 1/(1000000 / 1151167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (14077621 / 100000000) (140776211 / 1000000000) (Real.log (1151167 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1151167 / 1000000) = -Real.log (1000000 / 1151167) := by
    rw [show ((1151167 / 1000000) : ℝ) = ((1000000 / 1151167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (81946407 / 500000000) ≤ -Real.log (848833 / 1000000) ∧
    -Real.log (848833 / 1000000) ≤ (32778563 / 200000000) := by
  have h := checkLog_sound (w := (151167 / 1848833)) (n := 12)
    (lo := (81946407 / 500000000)) (hi := (32778563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 848833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 848833) = 1/(848833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-32778563 / 200000000) (-81946407 / 500000000) (Real.log (848833 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (141044597 / 1000000000) ≤ -Real.log (250000 / 287869) ∧
    -Real.log (250000 / 287869) ≤ (70522299 / 500000000) := by
  have h := checkLog_sound (w := (37869 / 537869)) (n := 12)
    (lo := (141044597 / 1000000000)) (hi := (70522299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287869 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287869 / 250000) = 1/(250000 / 287869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (141044597 / 1000000000) (70522299 / 500000000) (Real.log (287869 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (287869 / 250000) = -Real.log (250000 / 287869) := by
    rw [show ((287869 / 250000) : ℝ) = ((250000 / 287869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (164256909 / 1000000000) ≤ -Real.log (212131 / 250000) ∧
    -Real.log (212131 / 250000) ≤ (16425691 / 100000000) := by
  have h := checkLog_sound (w := (37869 / 462131)) (n := 12)
    (lo := (164256909 / 1000000000)) (hi := (16425691 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 212131) = 1/(212131 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-16425691 / 100000000) (-164256909 / 1000000000) (Real.log (212131 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (613463503 / 1000000000) ≤ -Real.log (100000000000 / 184681679177) ∧
    -Real.log (100000000000 / 184681679177) ≤ (38341469 / 62500000) := by
  have h := checkLog_sound (w := (84681679177 / 284681679177)) (n := 12)
    (lo := (613463503 / 1000000000)) (hi := (38341469 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184681679177 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184681679177 / 100000000000) = 1/(100000000000 / 184681679177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (613463503 / 1000000000) (38341469 / 62500000) (Real.log (184681679177 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (184681679177 / 100000000000) = -Real.log (100000000000 / 184681679177) := by
    rw [show ((184681679177 / 100000000000) : ℝ) = ((100000000000 / 184681679177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (614749381 / 1000000000) ≤ -Real.log (250000000000 / 462298274903) ∧
    -Real.log (250000000000 / 462298274903) ≤ (307374691 / 500000000) := by
  have h := checkLog_sound (w := (212298274903 / 712298274903)) (n := 12)
    (lo := (614749381 / 1000000000)) (hi := (307374691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((462298274903 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(462298274903 / 250000000000) = 1/(250000000000 / 462298274903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (614749381 / 1000000000) (307374691 / 500000000) (Real.log (462298274903 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (462298274903 / 250000000000) = -Real.log (250000000000 / 462298274903) := by
    rw [show ((462298274903 / 250000000000) : ℝ) = ((250000000000 / 462298274903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (428730571 / 1000000000) ≤ -Real.log (500000000000 / 767653661807) ∧
    -Real.log (500000000000 / 767653661807) ≤ (107182643 / 250000000) := by
  have h := checkLog_sound (w := (267653661807 / 1267653661807)) (n := 12)
    (lo := (428730571 / 1000000000)) (hi := (107182643 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((767653661807 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(767653661807 / 500000000000) = 1/(500000000000 / 767653661807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (428730571 / 1000000000) (107182643 / 250000000) (Real.log (767653661807 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (767653661807 / 500000000000) = -Real.log (500000000000 / 767653661807) := by
    rw [show ((767653661807 / 500000000000) : ℝ) = ((500000000000 / 767653661807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (214805971 / 500000000) ≤ -Real.log (250000000000 / 384165273617) ∧
    -Real.log (250000000000 / 384165273617) ≤ (429611943 / 1000000000) := by
  have h := checkLog_sound (w := (134165273617 / 634165273617)) (n := 12)
    (lo := (214805971 / 500000000)) (hi := (429611943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384165273617 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384165273617 / 250000000000) = 1/(250000000000 / 384165273617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (214805971 / 500000000) (429611943 / 1000000000) (Real.log (384165273617 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (384165273617 / 250000000000) = -Real.log (250000000000 / 384165273617) := by
    rw [show ((384165273617 / 250000000000) : ℝ) = ((250000000000 / 384165273617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (9520907 / 31250000) ≤ -Real.log (250000000000 / 339044016903) ∧
    -Real.log (250000000000 / 339044016903) ≤ (12186761 / 40000000) := by
  have h := checkLog_sound (w := (89044016903 / 589044016903)) (n := 12)
    (lo := (9520907 / 31250000)) (hi := (12186761 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339044016903 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339044016903 / 250000000000) = 1/(250000000000 / 339044016903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (9520907 / 31250000) (12186761 / 40000000) (Real.log (339044016903 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (339044016903 / 250000000000) = -Real.log (250000000000 / 339044016903) := by
    rw [show ((339044016903 / 250000000000) : ℝ) = ((250000000000 / 339044016903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (305301507 / 1000000000) ≤ -Real.log (125000000000 / 169629262107) ∧
    -Real.log (125000000000 / 169629262107) ≤ (76325377 / 250000000) := by
  have h := checkLog_sound (w := (44629262107 / 294629262107)) (n := 12)
    (lo := (305301507 / 1000000000)) (hi := (76325377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169629262107 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169629262107 / 125000000000) = 1/(125000000000 / 169629262107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (305301507 / 1000000000) (76325377 / 250000000) (Real.log (169629262107 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (169629262107 / 125000000000) = -Real.log (125000000000 / 169629262107) := by
    rw [show ((169629262107 / 125000000000) : ℝ) = ((125000000000 / 169629262107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (23212311 / 1000000000) ≤ -Real.log (61065938839 / 62500000000) ∧
    -Real.log (61065938839 / 62500000000) ≤ (2901539 / 125000000) := by
  have h := checkLog_sound (w := (1434061161 / 123565938839)) (n := 12)
    (lo := (23212311 / 1000000000)) (hi := (2901539 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61065938839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61065938839) = 1/(61065938839 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2901539 / 125000000) (-23212311 / 1000000000) (Real.log (61065938839 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (23116603 / 1000000000) ≤ -Real.log (977148538111 / 1000000000000) ∧
    -Real.log (977148538111 / 1000000000000) ≤ (5779151 / 250000000) := by
  have h := checkLog_sound (w := (22851461889 / 1977148538111)) (n := 12)
    (lo := (23116603 / 1000000000)) (hi := (5779151 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977148538111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977148538111) = 1/(977148538111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5779151 / 250000000) (-23116603 / 1000000000) (Real.log (977148538111 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell081
