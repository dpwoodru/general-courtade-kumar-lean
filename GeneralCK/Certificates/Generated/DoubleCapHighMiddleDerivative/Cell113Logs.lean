import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell113
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

theorem reflection_log_1_neg : (275202177 / 1000000000) ≤ -Real.log (2560 / 3371) ∧
    -Real.log (2560 / 3371) ≤ (137601089 / 500000000) := by
  have h := checkLog_sound (w := (811 / 5931)) (n := 12)
    (lo := (275202177 / 1000000000)) (hi := (137601089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3371 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3371 / 2560) = 1/(2560 / 3371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (275202177 / 1000000000) (137601089 / 500000000) (Real.log (3371 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3371 / 2560) = -Real.log (2560 / 3371) := by
    rw [show ((3371 / 2560) : ℝ) = ((2560 / 3371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (190481531 / 500000000) ≤ -Real.log (1749 / 2560) ∧
    -Real.log (1749 / 2560) ≤ (380963063 / 1000000000) := by
  have h := checkLog_sound (w := (811 / 4309)) (n := 12)
    (lo := (190481531 / 500000000)) (hi := (380963063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1749) = 1/(1749 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-380963063 / 1000000000) (-190481531 / 500000000) (Real.log (1749 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (137378553 / 500000000) ≤ -Real.log (5120 / 6739) ∧
    -Real.log (5120 / 6739) ≤ (274757107 / 1000000000) := by
  have h := checkLog_sound (w := (1619 / 11859)) (n := 12)
    (lo := (137378553 / 500000000)) (hi := (274757107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6739 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6739 / 5120) = 1/(5120 / 6739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (137378553 / 500000000) (274757107 / 1000000000) (Real.log (6739 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6739 / 5120) = -Real.log (5120 / 6739) := by
    rw [show ((6739 / 5120) : ℝ) = ((5120 / 6739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (380105797 / 1000000000) ≤ -Real.log (3501 / 5120) ∧
    -Real.log (3501 / 5120) ≤ (190052899 / 500000000) := by
  have h := checkLog_sound (w := (1619 / 8621)) (n := 12)
    (lo := (380105797 / 1000000000)) (hi := (190052899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3501) = 1/(3501 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-190052899 / 500000000) (-380105797 / 1000000000) (Real.log (3501 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (12661707 / 62500000) ≤ -Real.log (1000000 / 1224567) ∧
    -Real.log (1000000 / 1224567) ≤ (202587313 / 1000000000) := by
  have h := checkLog_sound (w := (224567 / 2224567)) (n := 12)
    (lo := (12661707 / 62500000)) (hi := (202587313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1224567 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1224567 / 1000000) = 1/(1000000 / 1224567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (12661707 / 62500000) (202587313 / 1000000000) (Real.log (1224567 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1224567 / 1000000) = -Real.log (1000000 / 1224567) := by
    rw [show ((1224567 / 1000000) : ℝ) = ((1000000 / 1224567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (50866739 / 200000000) ≤ -Real.log (775433 / 1000000) ∧
    -Real.log (775433 / 1000000) ≤ (993491 / 3906250) := by
  have h := checkLog_sound (w := (224567 / 1775433)) (n := 12)
    (lo := (50866739 / 200000000)) (hi := (993491 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 775433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 775433) = 1/(775433 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-993491 / 3906250) (-50866739 / 200000000) (Real.log (775433 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (25366381 / 125000000) ≤ -Real.log (250000 / 306247) ∧
    -Real.log (250000 / 306247) ≤ (202931049 / 1000000000) := by
  have h := checkLog_sound (w := (56247 / 556247)) (n := 12)
    (lo := (25366381 / 125000000)) (hi := (202931049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306247 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306247 / 250000) = 1/(250000 / 306247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (25366381 / 125000000) (202931049 / 1000000000) (Real.log (306247 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (306247 / 250000) = -Real.log (250000 / 306247) := by
    rw [show ((306247 / 250000) : ℝ) = ((250000 / 306247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (50975353 / 200000000) ≤ -Real.log (193753 / 250000) ∧
    -Real.log (193753 / 250000) ≤ (127438383 / 500000000) := by
  have h := checkLog_sound (w := (56247 / 443753)) (n := 12)
    (lo := (50975353 / 200000000)) (hi := (127438383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 193753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 193753) = 1/(193753 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-127438383 / 500000000) (-50975353 / 200000000) (Real.log (193753 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (149318739 / 1000000000) ≤ -Real.log (1000000 / 1161043) ∧
    -Real.log (1000000 / 1161043) ≤ (7465937 / 50000000) := by
  have h := checkLog_sound (w := (161043 / 2161043)) (n := 12)
    (lo := (149318739 / 1000000000)) (hi := (7465937 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161043 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161043 / 1000000) = 1/(1000000 / 1161043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (149318739 / 1000000000) (7465937 / 50000000) (Real.log (1161043 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1161043 / 1000000) = -Real.log (1000000 / 1161043) := by
    rw [show ((1161043 / 1000000) : ℝ) = ((1000000 / 1161043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (7023833 / 40000000) ≤ -Real.log (838957 / 1000000) ∧
    -Real.log (838957 / 1000000) ≤ (87797913 / 500000000) := by
  have h := checkLog_sound (w := (161043 / 1838957)) (n := 12)
    (lo := (7023833 / 40000000)) (hi := (87797913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 838957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 838957) = 1/(838957 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-87797913 / 500000000) (-7023833 / 40000000) (Real.log (838957 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (29917313 / 200000000) ≤ -Real.log (500000 / 580677) ∧
    -Real.log (500000 / 580677) ≤ (74793283 / 500000000) := by
  have h := checkLog_sound (w := (80677 / 1080677)) (n := 12)
    (lo := (29917313 / 200000000)) (hi := (74793283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((580677 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(580677 / 500000) = 1/(500000 / 580677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (29917313 / 200000000) (74793283 / 500000000) (Real.log (580677 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (580677 / 500000) = -Real.log (500000 / 580677) := by
    rw [show ((580677 / 500000) : ℝ) = ((500000 / 580677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1374739 / 7812500) ≤ -Real.log (419323 / 500000) ∧
    -Real.log (419323 / 500000) ≤ (175966593 / 1000000000) := by
  have h := checkLog_sound (w := (80677 / 919323)) (n := 12)
    (lo := (1374739 / 7812500)) (hi := (175966593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 419323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 419323) = 1/(419323 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-175966593 / 1000000000) (-1374739 / 7812500) (Real.log (419323 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (654862903 / 1000000000) ≤ -Real.log (31250000000 / 60152456441) ∧
    -Real.log (31250000000 / 60152456441) ≤ (81857863 / 125000000) := by
  have h := checkLog_sound (w := (28902456441 / 91402456441)) (n := 12)
    (lo := (654862903 / 1000000000)) (hi := (81857863 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60152456441 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60152456441 / 31250000000) = 1/(31250000000 / 60152456441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (654862903 / 1000000000) (81857863 / 125000000) (Real.log (60152456441 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (60152456441 / 31250000000) = -Real.log (31250000000 / 60152456441) := by
    rw [show ((60152456441 / 31250000000) : ℝ) = ((31250000000 / 60152456441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (16404131 / 25000000) ≤ -Real.log (250000000000 / 481846769583) ∧
    -Real.log (250000000000 / 481846769583) ≤ (656165241 / 1000000000) := by
  have h := checkLog_sound (w := (231846769583 / 731846769583)) (n := 12)
    (lo := (16404131 / 25000000)) (hi := (656165241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481846769583 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(481846769583 / 250000000000) = 1/(250000000000 / 481846769583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (16404131 / 25000000) (656165241 / 1000000000) (Real.log (481846769583 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (481846769583 / 250000000000) = -Real.log (250000000000 / 481846769583) := by
    rw [show ((481846769583 / 250000000000) : ℝ) = ((250000000000 / 481846769583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (28557563 / 62500000) ≤ -Real.log (50000000000 / 78960206749) ∧
    -Real.log (50000000000 / 78960206749) ≤ (456921009 / 1000000000) := by
  have h := checkLog_sound (w := (28960206749 / 128960206749)) (n := 12)
    (lo := (28557563 / 62500000)) (hi := (456921009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78960206749 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78960206749 / 50000000000) = 1/(50000000000 / 78960206749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (28557563 / 62500000) (456921009 / 1000000000) (Real.log (78960206749 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (78960206749 / 50000000000) = -Real.log (50000000000 / 78960206749) := by
    rw [show ((78960206749 / 50000000000) : ℝ) = ((50000000000 / 78960206749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (457807813 / 1000000000) ≤ -Real.log (500000000000 / 790302601767) ∧
    -Real.log (500000000000 / 790302601767) ≤ (228903907 / 500000000) := by
  have h := checkLog_sound (w := (290302601767 / 1290302601767)) (n := 12)
    (lo := (457807813 / 1000000000)) (hi := (228903907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((790302601767 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(790302601767 / 500000000000) = 1/(500000000000 / 790302601767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (457807813 / 1000000000) (228903907 / 500000000) (Real.log (790302601767 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (790302601767 / 500000000000) = -Real.log (500000000000 / 790302601767) := by
    rw [show ((790302601767 / 500000000000) : ℝ) = ((500000000000 / 790302601767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (81228641 / 250000000) ≤ -Real.log (500000000000 / 691956202761) ∧
    -Real.log (500000000000 / 691956202761) ≤ (64982913 / 200000000) := by
  have h := checkLog_sound (w := (191956202761 / 1191956202761)) (n := 12)
    (lo := (81228641 / 250000000)) (hi := (64982913 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691956202761 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691956202761 / 500000000000) = 1/(500000000000 / 691956202761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (81228641 / 250000000) (64982913 / 200000000) (Real.log (691956202761 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (691956202761 / 500000000000) = -Real.log (500000000000 / 691956202761) := by
    rw [show ((691956202761 / 500000000000) : ℝ) = ((500000000000 / 691956202761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (162776579 / 500000000) ≤ -Real.log (10000000000 / 13847964457) ∧
    -Real.log (10000000000 / 13847964457) ≤ (325553159 / 1000000000) := by
  have h := checkLog_sound (w := (3847964457 / 23847964457)) (n := 12)
    (lo := (162776579 / 500000000)) (hi := (325553159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13847964457 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13847964457 / 10000000000) = 1/(10000000000 / 13847964457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (162776579 / 500000000) (325553159 / 1000000000) (Real.log (13847964457 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13847964457 / 10000000000) = -Real.log (10000000000 / 13847964457) := by
    rw [show ((13847964457 / 10000000000) : ℝ) = ((10000000000 / 13847964457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (13190013 / 500000000) ≤ -Real.log (243491221671 / 250000000000) ∧
    -Real.log (243491221671 / 250000000000) ≤ (26380027 / 1000000000) := by
  have h := checkLog_sound (w := (6508778329 / 493491221671)) (n := 12)
    (lo := (13190013 / 500000000)) (hi := (26380027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243491221671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243491221671) = 1/(243491221671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-26380027 / 1000000000) (-13190013 / 500000000) (Real.log (243491221671 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (13138543 / 500000000) ≤ -Real.log (974065152151 / 1000000000000) ∧
    -Real.log (974065152151 / 1000000000000) ≤ (26277087 / 1000000000) := by
  have h := checkLog_sound (w := (25934847849 / 1974065152151)) (n := 12)
    (lo := (13138543 / 500000000)) (hi := (26277087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974065152151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974065152151) = 1/(974065152151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-26277087 / 1000000000) (-13138543 / 500000000) (Real.log (974065152151 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell113
