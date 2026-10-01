import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell115
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

theorem reflection_log_1_neg : (11043669 / 40000000) ≤ -Real.log (1280 / 1687) ∧
    -Real.log (1280 / 1687) ≤ (138045863 / 500000000) := by
  have h := checkLog_sound (w := (407 / 2967)) (n := 12)
    (lo := (11043669 / 40000000)) (hi := (138045863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1687 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1687 / 1280) = 1/(1280 / 1687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11043669 / 40000000) (138045863 / 500000000) (Real.log (1687 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1687 / 1280) = -Real.log (1280 / 1687) := by
    rw [show ((1687 / 1280) : ℝ) = ((1280 / 1687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (382679801 / 1000000000) ≤ -Real.log (873 / 1280) ∧
    -Real.log (873 / 1280) ≤ (191339901 / 500000000) := by
  have h := checkLog_sound (w := (407 / 2153)) (n := 12)
    (lo := (382679801 / 1000000000)) (hi := (191339901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 873) = 1/(873 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-191339901 / 500000000) (-382679801 / 1000000000) (Real.log (873 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5512941 / 20000000) ≤ -Real.log (1024 / 1349) ∧
    -Real.log (1024 / 1349) ≤ (275647051 / 1000000000) := by
  have h := checkLog_sound (w := (325 / 2373)) (n := 12)
    (lo := (5512941 / 20000000)) (hi := (275647051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1349 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1349 / 1024) = 1/(1024 / 1349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (5512941 / 20000000) (275647051 / 1000000000) (Real.log (1349 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1349 / 1024) = -Real.log (1024 / 1349) := by
    rw [show ((1349 / 1024) : ℝ) = ((1024 / 1349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (381821063 / 1000000000) ≤ -Real.log (699 / 1024) ∧
    -Real.log (699 / 1024) ≤ (47727633 / 125000000) := by
  have h := checkLog_sound (w := (325 / 1723)) (n := 12)
    (lo := (381821063 / 1000000000)) (hi := (47727633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 699) = 1/(699 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-47727633 / 125000000) (-381821063 / 1000000000) (Real.log (699 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (203272217 / 1000000000) ≤ -Real.log (500000 / 612703) ∧
    -Real.log (500000 / 612703) ≤ (101636109 / 500000000) := by
  have h := checkLog_sound (w := (112703 / 1112703)) (n := 12)
    (lo := (203272217 / 1000000000)) (hi := (101636109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612703 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612703 / 500000) = 1/(500000 / 612703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (203272217 / 1000000000) (101636109 / 500000000) (Real.log (612703 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (612703 / 500000) = -Real.log (500000 / 612703) := by
    rw [show ((612703 / 500000) : ℝ) = ((500000 / 612703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (255416257 / 1000000000) ≤ -Real.log (387297 / 500000) ∧
    -Real.log (387297 / 500000) ≤ (127708129 / 500000000) := by
  have h := checkLog_sound (w := (112703 / 887297)) (n := 12)
    (lo := (255416257 / 1000000000)) (hi := (127708129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 387297) = 1/(387297 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-127708129 / 500000000) (-255416257 / 1000000000) (Real.log (387297 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (101807859 / 500000000) ≤ -Real.log (1000000 / 1225827) ∧
    -Real.log (1000000 / 1225827) ≤ (203615719 / 1000000000) := by
  have h := checkLog_sound (w := (225827 / 2225827)) (n := 12)
    (lo := (101807859 / 500000000)) (hi := (203615719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1225827 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1225827 / 1000000) = 1/(1000000 / 1225827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (101807859 / 500000000) (203615719 / 1000000000) (Real.log (1225827 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1225827 / 1000000) = -Real.log (1000000 / 1225827) := by
    rw [show ((1225827 / 1000000) : ℝ) = ((1000000 / 1225827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (63989979 / 250000000) ≤ -Real.log (774173 / 1000000) ∧
    -Real.log (774173 / 1000000) ≤ (255959917 / 1000000000) := by
  have h := checkLog_sound (w := (225827 / 1774173)) (n := 12)
    (lo := (63989979 / 250000000)) (hi := (255959917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 774173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 774173) = 1/(774173 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-255959917 / 1000000000) (-63989979 / 250000000) (Real.log (774173 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (74925869 / 500000000) ≤ -Real.log (500000 / 580831) ∧
    -Real.log (500000 / 580831) ≤ (149851739 / 1000000000) := by
  have h := checkLog_sound (w := (80831 / 1080831)) (n := 12)
    (lo := (74925869 / 500000000)) (hi := (149851739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((580831 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(580831 / 500000) = 1/(500000 / 580831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (74925869 / 500000000) (149851739 / 1000000000) (Real.log (580831 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (580831 / 500000) = -Real.log (500000 / 580831) := by
    rw [show ((580831 / 500000) : ℝ) = ((500000 / 580831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (88166959 / 500000000) ≤ -Real.log (419169 / 500000) ∧
    -Real.log (419169 / 500000) ≤ (176333919 / 1000000000) := by
  have h := checkLog_sound (w := (80831 / 919169)) (n := 12)
    (lo := (88166959 / 500000000)) (hi := (176333919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 419169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 419169) = 1/(419169 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-176333919 / 1000000000) (-88166959 / 500000000) (Real.log (419169 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (75059711 / 500000000) ≤ -Real.log (1000000 / 1161973) ∧
    -Real.log (1000000 / 1161973) ≤ (150119423 / 1000000000) := by
  have h := checkLog_sound (w := (161973 / 2161973)) (n := 12)
    (lo := (75059711 / 500000000)) (hi := (150119423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161973 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161973 / 1000000) = 1/(1000000 / 1161973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (75059711 / 500000000) (150119423 / 1000000000) (Real.log (1161973 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1161973 / 1000000) = -Real.log (1000000 / 1161973) := by
    rw [show ((1161973 / 1000000) : ℝ) = ((1000000 / 1161973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (176704959 / 1000000000) ≤ -Real.log (838027 / 1000000) ∧
    -Real.log (838027 / 1000000) ≤ (552203 / 3125000) := by
  have h := checkLog_sound (w := (161973 / 1838027)) (n := 12)
    (lo := (176704959 / 1000000000)) (hi := (552203 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 838027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 838027) = 1/(838027 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-552203 / 3125000) (-176704959 / 1000000000) (Real.log (838027 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (657468113 / 1000000000) ≤ -Real.log (500000000000 / 964949928469) ∧
    -Real.log (500000000000 / 964949928469) ≤ (328734057 / 500000000) := by
  have h := checkLog_sound (w := (464949928469 / 1464949928469)) (n := 12)
    (lo := (657468113 / 1000000000)) (hi := (328734057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((964949928469 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(964949928469 / 500000000000) = 1/(500000000000 / 964949928469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (657468113 / 1000000000) (328734057 / 500000000) (Real.log (964949928469 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (964949928469 / 500000000000) = -Real.log (500000000000 / 964949928469) := by
    rw [show ((964949928469 / 500000000000) : ℝ) = ((500000000000 / 964949928469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (329385763 / 500000000) ≤ -Real.log (250000000000 / 483104238259) ∧
    -Real.log (250000000000 / 483104238259) ≤ (658771527 / 1000000000) := by
  have h := checkLog_sound (w := (233104238259 / 733104238259)) (n := 12)
    (lo := (329385763 / 500000000)) (hi := (658771527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483104238259 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483104238259 / 250000000000) = 1/(250000000000 / 483104238259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (329385763 / 500000000) (658771527 / 1000000000) (Real.log (483104238259 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (483104238259 / 250000000000) = -Real.log (250000000000 / 483104238259) := by
    rw [show ((483104238259 / 250000000000) : ℝ) = ((250000000000 / 483104238259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (18347539 / 40000000) ≤ -Real.log (250000000000 / 395499448743) ∧
    -Real.log (250000000000 / 395499448743) ≤ (114672119 / 250000000) := by
  have h := checkLog_sound (w := (145499448743 / 645499448743)) (n := 12)
    (lo := (18347539 / 40000000)) (hi := (114672119 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395499448743 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395499448743 / 250000000000) = 1/(250000000000 / 395499448743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (18347539 / 40000000) (114672119 / 250000000) (Real.log (395499448743 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (395499448743 / 250000000000) = -Real.log (250000000000 / 395499448743) := by
    rw [show ((395499448743 / 250000000000) : ℝ) = ((250000000000 / 395499448743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (229787817 / 500000000) ≤ -Real.log (500000000000 / 791700950563) ∧
    -Real.log (500000000000 / 791700950563) ≤ (91915127 / 200000000) := by
  have h := checkLog_sound (w := (291700950563 / 1291700950563)) (n := 12)
    (lo := (229787817 / 500000000)) (hi := (91915127 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791700950563 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791700950563 / 500000000000) = 1/(500000000000 / 791700950563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (229787817 / 500000000) (91915127 / 200000000) (Real.log (791700950563 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (791700950563 / 500000000000) = -Real.log (500000000000 / 791700950563) := by
    rw [show ((791700950563 / 500000000000) : ℝ) = ((500000000000 / 791700950563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (40773207 / 125000000) ≤ -Real.log (250000000000 / 346418151151) ∧
    -Real.log (250000000000 / 346418151151) ≤ (326185657 / 1000000000) := by
  have h := checkLog_sound (w := (96418151151 / 596418151151)) (n := 12)
    (lo := (40773207 / 125000000)) (hi := (326185657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346418151151 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346418151151 / 250000000000) = 1/(250000000000 / 346418151151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (40773207 / 125000000) (326185657 / 1000000000) (Real.log (346418151151 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (346418151151 / 250000000000) = -Real.log (250000000000 / 346418151151) := by
    rw [show ((346418151151 / 250000000000) : ℝ) = ((250000000000 / 346418151151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (326824381 / 1000000000) ≤ -Real.log (500000000000 / 693278975499) ∧
    -Real.log (500000000000 / 693278975499) ≤ (163412191 / 500000000) := by
  have h := checkLog_sound (w := (193278975499 / 1193278975499)) (n := 12)
    (lo := (326824381 / 1000000000)) (hi := (163412191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693278975499 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693278975499 / 500000000000) = 1/(500000000000 / 693278975499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (326824381 / 1000000000) (163412191 / 500000000) (Real.log (693278975499 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (693278975499 / 500000000000) = -Real.log (500000000000 / 693278975499) := by
    rw [show ((693278975499 / 500000000000) : ℝ) = ((500000000000 / 693278975499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (26585537 / 1000000000) ≤ -Real.log (973764747271 / 1000000000000) ∧
    -Real.log (973764747271 / 1000000000000) ≤ (13292769 / 500000000) := by
  have h := checkLog_sound (w := (26235252729 / 1973764747271)) (n := 12)
    (lo := (26585537 / 1000000000)) (hi := (13292769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973764747271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973764747271) = 1/(973764747271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-13292769 / 500000000) (-26585537 / 1000000000) (Real.log (973764747271 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1324109 / 50000000) ≤ -Real.log (243466349439 / 250000000000) ∧
    -Real.log (243466349439 / 250000000000) ≤ (26482181 / 1000000000) := by
  have h := checkLog_sound (w := (6533650561 / 493466349439)) (n := 12)
    (lo := (1324109 / 50000000)) (hi := (26482181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243466349439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243466349439) = 1/(243466349439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-26482181 / 1000000000) (-1324109 / 50000000) (Real.log (243466349439 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell115
