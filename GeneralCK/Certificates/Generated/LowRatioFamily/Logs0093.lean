import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5952_neg : (92493489 / 1000000000) ≤ -Real.log (500000 / 548453) ∧
    -Real.log (500000 / 548453) ≤ (9249349 / 100000000) := by
  have h := checkLog_sound (w := (48453 / 1048453)) (n := 12)
    (lo := (92493489 / 1000000000)) (hi := (9249349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548453 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548453 / 500000) = 1/(500000 / 548453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5952 : Bounds (92493489 / 1000000000) (9249349 / 100000000) (Real.log (548453 / 500000)) := by
  have h := reflection_log_5952_neg
  have he : Real.log (548453 / 500000) = -Real.log (500000 / 548453) := by
    rw [show ((548453 / 500000) : ℝ) = ((500000 / 548453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5953_neg : (101928633 / 1000000000) ≤ -Real.log (451547 / 500000) ∧
    -Real.log (451547 / 500000) ≤ (50964317 / 500000000) := by
  have h := checkLog_sound (w := (48453 / 951547)) (n := 12)
    (lo := (101928633 / 1000000000)) (hi := (50964317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451547) = 1/(451547 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5953 : Bounds (-50964317 / 500000000) (-101928633 / 1000000000) (Real.log (451547 / 500000)) := by
  have h := reflection_log_5953_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5954_neg : (23178977 / 250000000) ≤ -Real.log (20000 / 21943) ∧
    -Real.log (20000 / 21943) ≤ (92715909 / 1000000000) := by
  have h := checkLog_sound (w := (1943 / 41943)) (n := 12)
    (lo := (23178977 / 250000000)) (hi := (92715909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21943 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21943 / 20000) = 1/(20000 / 21943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5954 : Bounds (23178977 / 250000000) (92715909 / 1000000000) (Real.log (21943 / 20000)) := by
  have h := reflection_log_5954_neg
  have he : Real.log (21943 / 20000) = -Real.log (20000 / 21943) := by
    rw [show ((21943 / 20000) : ℝ) = ((20000 / 21943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5955_neg : (25549713 / 250000000) ≤ -Real.log (18057 / 20000) ∧
    -Real.log (18057 / 20000) ≤ (102198853 / 1000000000) := by
  have h := checkLog_sound (w := (1943 / 38057)) (n := 12)
    (lo := (25549713 / 250000000)) (hi := (102198853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 18057) = 1/(18057 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5955 : Bounds (-102198853 / 1000000000) (-25549713 / 250000000) (Real.log (18057 / 20000)) := by
  have h := reflection_log_5955_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5956_neg : (9482943 / 1000000000) ≤ -Real.log (396224751 / 400000000) ∧
    -Real.log (396224751 / 400000000) ≤ (148171 / 15625000) := by
  have h := checkLog_sound (w := (3775249 / 796224751)) (n := 12)
    (lo := (9482943 / 1000000000)) (hi := (148171 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 396224751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 396224751) = 1/(396224751 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5956 : Bounds (-148171 / 15625000) (-9482943 / 1000000000) (Real.log (396224751 / 400000000)) := by
  have h := reflection_log_5956_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5957_neg : (1179393 / 125000000) ≤ -Real.log (247652306791 / 250000000000) ∧
    -Real.log (247652306791 / 250000000000) ≤ (1887029 / 200000000) := by
  have h := checkLog_sound (w := (2347693209 / 497652306791)) (n := 12)
    (lo := (1179393 / 125000000)) (hi := (1887029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247652306791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247652306791) = 1/(247652306791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5957 : Bounds (-1887029 / 200000000) (-1179393 / 125000000) (Real.log (247652306791 / 250000000000)) := by
  have h := reflection_log_5957_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5958_neg : (97211061 / 500000000) ≤ -Real.log (250000000000 / 303652222249) ∧
    -Real.log (250000000000 / 303652222249) ≤ (194422123 / 1000000000) := by
  have h := checkLog_sound (w := (53652222249 / 553652222249)) (n := 12)
    (lo := (97211061 / 500000000)) (hi := (194422123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303652222249 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303652222249 / 250000000000) = 1/(250000000000 / 303652222249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5958 : Bounds (97211061 / 500000000) (194422123 / 1000000000) (Real.log (303652222249 / 250000000000)) := by
  have h := reflection_log_5958_neg
  have he : Real.log (303652222249 / 250000000000) = -Real.log (250000000000 / 303652222249) := by
    rw [show ((303652222249 / 250000000000) : ℝ) = ((250000000000 / 303652222249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5959_neg : (4872869 / 25000000) ≤ -Real.log (500000000000 / 607603699397) ∧
    -Real.log (500000000000 / 607603699397) ≤ (194914761 / 1000000000) := by
  have h := checkLog_sound (w := (107603699397 / 1107603699397)) (n := 12)
    (lo := (4872869 / 25000000)) (hi := (194914761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607603699397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607603699397 / 500000000000) = 1/(500000000000 / 607603699397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5959 : Bounds (4872869 / 25000000) (194914761 / 1000000000) (Real.log (607603699397 / 500000000000)) := by
  have h := reflection_log_5959_neg
  have he : Real.log (607603699397 / 500000000000) = -Real.log (500000000000 / 607603699397) := by
    rw [show ((607603699397 / 500000000000) : ℝ) = ((500000000000 / 607603699397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5960_neg : (390279577 / 1000000000) ≤ -Real.log (50000000000 / 73869689087) ∧
    -Real.log (50000000000 / 73869689087) ≤ (195139789 / 500000000) := by
  have h := checkLog_sound (w := (23869689087 / 123869689087)) (n := 12)
    (lo := (390279577 / 1000000000)) (hi := (195139789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73869689087 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73869689087 / 50000000000) = 1/(50000000000 / 73869689087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5960 : Bounds (390279577 / 1000000000) (195139789 / 500000000) (Real.log (73869689087 / 50000000000)) := by
  have h := reflection_log_5960_neg
  have he : Real.log (73869689087 / 50000000000) = -Real.log (50000000000 / 73869689087) := by
    rw [show ((73869689087 / 50000000000) : ℝ) = ((50000000000 / 73869689087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5961_neg : (195243647 / 500000000) ≤ -Real.log (500000000000 / 738850346879) ∧
    -Real.log (500000000000 / 738850346879) ≤ (78097459 / 200000000) := by
  have h := checkLog_sound (w := (238850346879 / 1238850346879)) (n := 12)
    (lo := (195243647 / 500000000)) (hi := (78097459 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738850346879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738850346879 / 500000000000) = 1/(500000000000 / 738850346879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5961 : Bounds (195243647 / 500000000) (78097459 / 200000000) (Real.log (738850346879 / 500000000000)) := by
  have h := reflection_log_5961_neg
  have he : Real.log (738850346879 / 500000000000) = -Real.log (500000000000 / 738850346879) := by
    rw [show ((738850346879 / 500000000000) : ℝ) = ((500000000000 / 738850346879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5962_neg : (176387317 / 1000000000) ≤ -Real.log (10000 / 11929) ∧
    -Real.log (10000 / 11929) ≤ (88193659 / 500000000) := by
  have h := checkLog_sound (w := (1929 / 21929)) (n := 12)
    (lo := (176387317 / 1000000000)) (hi := (88193659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11929 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11929 / 10000) = 1/(10000 / 11929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5962 : Bounds (176387317 / 1000000000) (88193659 / 500000000) (Real.log (11929 / 10000)) := by
  have h := reflection_log_5962_neg
  have he : Real.log (11929 / 10000) = -Real.log (10000 / 11929) := by
    rw [show ((11929 / 10000) : ℝ) = ((10000 / 11929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5963_neg : (107153851 / 500000000) ≤ -Real.log (8071 / 10000) ∧
    -Real.log (8071 / 10000) ≤ (214307703 / 1000000000) := by
  have h := checkLog_sound (w := (1929 / 18071)) (n := 12)
    (lo := (107153851 / 500000000)) (hi := (214307703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8071) = 1/(8071 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5963 : Bounds (-214307703 / 1000000000) (-107153851 / 500000000) (Real.log (8071 / 10000)) := by
  have h := reflection_log_5963_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5964_neg : (192881 / 1000000000) ≤ -Real.log (10000000 / 10001929) ∧
    -Real.log (10000000 / 10001929) ≤ (96441 / 500000000) := by
  have h := checkLog_sound (w := (1929 / 20001929)) (n := 12)
    (lo := (192881 / 1000000000)) (hi := (96441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001929 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001929 / 10000000) = 1/(10000000 / 10001929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5964 : Bounds (192881 / 1000000000) (96441 / 500000000) (Real.log (10001929 / 10000000)) := by
  have h := reflection_log_5964_neg
  have he : Real.log (10001929 / 10000000) = -Real.log (10000000 / 10001929) := by
    rw [show ((10001929 / 10000000) : ℝ) = ((10000000 / 10001929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5965_neg : (96459 / 500000000) ≤ -Real.log (9998071 / 10000000) ∧
    -Real.log (9998071 / 10000000) ≤ (192919 / 1000000000) := by
  have h := checkLog_sound (w := (1929 / 19998071)) (n := 12)
    (lo := (96459 / 500000000)) (hi := (192919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998071) = 1/(9998071 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5965 : Bounds (-192919 / 1000000000) (-96459 / 500000000) (Real.log (9998071 / 10000000)) := by
  have h := reflection_log_5965_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5966_neg : (46269991 / 500000000) ≤ -Real.log (1000000 / 1096957) ∧
    -Real.log (1000000 / 1096957) ≤ (92539983 / 1000000000) := by
  have h := checkLog_sound (w := (96957 / 2096957)) (n := 12)
    (lo := (46269991 / 500000000)) (hi := (92539983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096957 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096957 / 1000000) = 1/(1000000 / 1096957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5966 : Bounds (46269991 / 500000000) (92539983 / 1000000000) (Real.log (1096957 / 1000000)) := by
  have h := reflection_log_5966_neg
  have he : Real.log (1096957 / 1000000) = -Real.log (1000000 / 1096957) := by
    rw [show ((1096957 / 1000000) : ℝ) = ((1000000 / 1096957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5967_neg : (101985107 / 1000000000) ≤ -Real.log (903043 / 1000000) ∧
    -Real.log (903043 / 1000000) ≤ (25496277 / 250000000) := by
  have h := checkLog_sound (w := (96957 / 1903043)) (n := 12)
    (lo := (101985107 / 1000000000)) (hi := (25496277 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903043) = 1/(903043 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5967 : Bounds (-25496277 / 250000000) (-101985107 / 1000000000) (Real.log (903043 / 1000000)) := by
  have h := reflection_log_5967_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5968_neg : (92762391 / 1000000000) ≤ -Real.log (1000000 / 1097201) ∧
    -Real.log (1000000 / 1097201) ≤ (11595299 / 125000000) := by
  have h := checkLog_sound (w := (97201 / 2097201)) (n := 12)
    (lo := (92762391 / 1000000000)) (hi := (11595299 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097201 / 1000000) = 1/(1000000 / 1097201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5968 : Bounds (92762391 / 1000000000) (11595299 / 125000000) (Real.log (1097201 / 1000000)) := by
  have h := reflection_log_5968_neg
  have he : Real.log (1097201 / 1000000) = -Real.log (1000000 / 1097201) := by
    rw [show ((1097201 / 1000000) : ℝ) = ((1000000 / 1097201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5969_neg : (102255341 / 1000000000) ≤ -Real.log (902799 / 1000000) ∧
    -Real.log (902799 / 1000000) ≤ (51127671 / 500000000) := by
  have h := checkLog_sound (w := (97201 / 1902799)) (n := 12)
    (lo := (102255341 / 1000000000)) (hi := (51127671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902799) = 1/(902799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5969 : Bounds (-51127671 / 500000000) (-102255341 / 1000000000) (Real.log (902799 / 1000000)) := by
  have h := reflection_log_5969_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5970_neg : (189859 / 20000000) ≤ -Real.log (990551965599 / 1000000000000) ∧
    -Real.log (990551965599 / 1000000000000) ≤ (9492951 / 1000000000) := by
  have h := checkLog_sound (w := (9448034401 / 1990551965599)) (n := 12)
    (lo := (189859 / 20000000)) (hi := (9492951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990551965599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990551965599) = 1/(990551965599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5970 : Bounds (-9492951 / 1000000000) (-189859 / 20000000) (Real.log (990551965599 / 1000000000000)) := by
  have h := reflection_log_5970_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5971_neg : (2361281 / 250000000) ≤ -Real.log (990599340151 / 1000000000000) ∧
    -Real.log (990599340151 / 1000000000000) ≤ (75561 / 8000000) := by
  have h := checkLog_sound (w := (9400659849 / 1990599340151)) (n := 12)
    (lo := (2361281 / 250000000)) (hi := (75561 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990599340151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990599340151) = 1/(990599340151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5971 : Bounds (-75561 / 8000000) (-2361281 / 250000000) (Real.log (990599340151 / 1000000000000)) := by
  have h := reflection_log_5971_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5972_neg : (19452509 / 100000000) ≤ -Real.log (500000000000 / 607366980309) ∧
    -Real.log (500000000000 / 607366980309) ≤ (194525091 / 1000000000) := by
  have h := checkLog_sound (w := (107366980309 / 1107366980309)) (n := 12)
    (lo := (19452509 / 100000000)) (hi := (194525091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607366980309 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607366980309 / 500000000000) = 1/(500000000000 / 607366980309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5972 : Bounds (19452509 / 100000000) (194525091 / 1000000000) (Real.log (607366980309 / 500000000000)) := by
  have h := reflection_log_5972_neg
  have he : Real.log (607366980309 / 500000000000) = -Real.log (500000000000 / 607366980309) := by
    rw [show ((607366980309 / 500000000000) : ℝ) = ((500000000000 / 607366980309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5973_neg : (195017733 / 1000000000) ≤ -Real.log (100000000000 / 121533253803) ∧
    -Real.log (100000000000 / 121533253803) ≤ (97508867 / 500000000) := by
  have h := checkLog_sound (w := (21533253803 / 221533253803)) (n := 12)
    (lo := (195017733 / 1000000000)) (hi := (97508867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121533253803 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121533253803 / 100000000000) = 1/(100000000000 / 121533253803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5973 : Bounds (195017733 / 1000000000) (97508867 / 500000000) (Real.log (121533253803 / 100000000000)) := by
  have h := reflection_log_5973_neg
  have he : Real.log (121533253803 / 100000000000) = -Real.log (100000000000 / 121533253803) := by
    rw [show ((121533253803 / 100000000000) : ℝ) = ((100000000000 / 121533253803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5974_neg : (195243647 / 500000000) ≤ -Real.log (250000000000 / 369425173439) ∧
    -Real.log (250000000000 / 369425173439) ≤ (78097459 / 200000000) := by
  have h := checkLog_sound (w := (119425173439 / 619425173439)) (n := 12)
    (lo := (195243647 / 500000000)) (hi := (78097459 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369425173439 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369425173439 / 250000000000) = 1/(250000000000 / 369425173439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5974 : Bounds (195243647 / 500000000) (78097459 / 200000000) (Real.log (369425173439 / 250000000000)) := by
  have h := reflection_log_5974_neg
  have he : Real.log (369425173439 / 250000000000) = -Real.log (250000000000 / 369425173439) := by
    rw [show ((369425173439 / 250000000000) : ℝ) = ((250000000000 / 369425173439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5975_neg : (390695019 / 1000000000) ≤ -Real.log (31250000000 / 46187740057) ∧
    -Real.log (31250000000 / 46187740057) ≤ (19534751 / 50000000) := by
  have h := checkLog_sound (w := (14937740057 / 77437740057)) (n := 12)
    (lo := (390695019 / 1000000000)) (hi := (19534751 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46187740057 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46187740057 / 31250000000) = 1/(31250000000 / 46187740057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5975 : Bounds (390695019 / 1000000000) (19534751 / 50000000) (Real.log (46187740057 / 31250000000)) := by
  have h := reflection_log_5975_neg
  have he : Real.log (46187740057 / 31250000000) = -Real.log (31250000000 / 46187740057) := by
    rw [show ((46187740057 / 31250000000) : ℝ) = ((31250000000 / 46187740057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5976_neg : (176471143 / 1000000000) ≤ -Real.log (1000 / 1193) ∧
    -Real.log (1000 / 1193) ≤ (22058893 / 125000000) := by
  have h := checkLog_sound (w := (193 / 2193)) (n := 12)
    (lo := (176471143 / 1000000000)) (hi := (22058893 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193 / 1000) = 1/(1000 / 1193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5976 : Bounds (176471143 / 1000000000) (22058893 / 125000000) (Real.log (1193 / 1000)) := by
  have h := reflection_log_5976_neg
  have he : Real.log (1193 / 1000) = -Real.log (1000 / 1193) := by
    rw [show ((1193 / 1000) : ℝ) = ((1000 / 1193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5977_neg : (21443161 / 100000000) ≤ -Real.log (807 / 1000) ∧
    -Real.log (807 / 1000) ≤ (214431611 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 1807)) (n := 12)
    (lo := (21443161 / 100000000)) (hi := (214431611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 807) = 1/(807 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5977 : Bounds (-214431611 / 1000000000) (-21443161 / 100000000) (Real.log (807 / 1000)) := by
  have h := reflection_log_5977_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5978_neg : (192981 / 1000000000) ≤ -Real.log (1000000 / 1000193) ∧
    -Real.log (1000000 / 1000193) ≤ (96491 / 500000000) := by
  have h := checkLog_sound (w := (193 / 2000193)) (n := 12)
    (lo := (192981 / 1000000000)) (hi := (96491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000193 / 1000000) = 1/(1000000 / 1000193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5978 : Bounds (192981 / 1000000000) (96491 / 500000000) (Real.log (1000193 / 1000000)) := by
  have h := reflection_log_5978_neg
  have he : Real.log (1000193 / 1000000) = -Real.log (1000000 / 1000193) := by
    rw [show ((1000193 / 1000000) : ℝ) = ((1000000 / 1000193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5979_neg : (96509 / 500000000) ≤ -Real.log (999807 / 1000000) ∧
    -Real.log (999807 / 1000000) ≤ (193019 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 1999807)) (n := 12)
    (lo := (96509 / 500000000)) (hi := (193019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999807) = 1/(999807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5979 : Bounds (-193019 / 1000000000) (-96509 / 500000000) (Real.log (999807 / 1000000)) := by
  have h := reflection_log_5979_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5980_neg : (92586473 / 1000000000) ≤ -Real.log (62500 / 68563) ∧
    -Real.log (62500 / 68563) ≤ (46293237 / 500000000) := by
  have h := checkLog_sound (w := (6063 / 131063)) (n := 12)
    (lo := (92586473 / 1000000000)) (hi := (46293237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68563 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68563 / 62500) = 1/(62500 / 68563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5980 : Bounds (92586473 / 1000000000) (46293237 / 500000000) (Real.log (68563 / 62500)) := by
  have h := reflection_log_5980_neg
  have he : Real.log (68563 / 62500) = -Real.log (62500 / 68563) := by
    rw [show ((68563 / 62500) : ℝ) = ((62500 / 68563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5981_neg : (6377599 / 62500000) ≤ -Real.log (56437 / 62500) ∧
    -Real.log (56437 / 62500) ≤ (20408317 / 200000000) := by
  have h := checkLog_sound (w := (6063 / 118937)) (n := 12)
    (lo := (6377599 / 62500000)) (hi := (20408317 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56437) = 1/(56437 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5981 : Bounds (-20408317 / 200000000) (-6377599 / 62500000) (Real.log (56437 / 62500)) := by
  have h := reflection_log_5981_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5982_neg : (11601109 / 125000000) ≤ -Real.log (250000 / 274313) ∧
    -Real.log (250000 / 274313) ≤ (92808873 / 1000000000) := by
  have h := checkLog_sound (w := (24313 / 524313)) (n := 12)
    (lo := (11601109 / 125000000)) (hi := (92808873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274313 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274313 / 250000) = 1/(250000 / 274313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5982 : Bounds (11601109 / 125000000) (92808873 / 1000000000) (Real.log (274313 / 250000)) := by
  have h := reflection_log_5982_neg
  have he : Real.log (274313 / 250000) = -Real.log (250000 / 274313) := by
    rw [show ((274313 / 250000) : ℝ) = ((250000 / 274313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5983_neg : (51155917 / 500000000) ≤ -Real.log (225687 / 250000) ∧
    -Real.log (225687 / 250000) ≤ (20462367 / 200000000) := by
  have h := checkLog_sound (w := (24313 / 475687)) (n := 12)
    (lo := (51155917 / 500000000)) (hi := (20462367 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225687) = 1/(225687 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5983 : Bounds (-20462367 / 200000000) (-51155917 / 500000000) (Real.log (225687 / 250000)) := by
  have h := reflection_log_5983_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5984_neg : (9502961 / 1000000000) ≤ -Real.log (61908878031 / 62500000000) ∧
    -Real.log (61908878031 / 62500000000) ≤ (4751481 / 500000000) := by
  have h := checkLog_sound (w := (591121969 / 124408878031)) (n := 12)
    (lo := (9502961 / 1000000000)) (hi := (4751481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61908878031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61908878031) = 1/(61908878031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5984 : Bounds (-4751481 / 500000000) (-9502961 / 1000000000) (Real.log (61908878031 / 62500000000)) := by
  have h := reflection_log_5984_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5985_neg : (9455111 / 1000000000) ≤ -Real.log (3869490031 / 3906250000) ∧
    -Real.log (3869490031 / 3906250000) ≤ (1181889 / 125000000) := by
  have h := checkLog_sound (w := (36759969 / 7775740031)) (n := 12)
    (lo := (9455111 / 1000000000)) (hi := (1181889 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3869490031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3869490031) = 1/(3869490031 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5985 : Bounds (-1181889 / 125000000) (-9455111 / 1000000000) (Real.log (3869490031 / 3906250000)) := by
  have h := reflection_log_5985_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5986_neg : (97314029 / 500000000) ≤ -Real.log (100000000000 / 121485904637) ∧
    -Real.log (100000000000 / 121485904637) ≤ (194628059 / 1000000000) := by
  have h := checkLog_sound (w := (21485904637 / 221485904637)) (n := 12)
    (lo := (97314029 / 500000000)) (hi := (194628059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121485904637 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121485904637 / 100000000000) = 1/(100000000000 / 121485904637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5986 : Bounds (97314029 / 500000000) (194628059 / 1000000000) (Real.log (121485904637 / 100000000000)) := by
  have h := reflection_log_5986_neg
  have he : Real.log (121485904637 / 100000000000) = -Real.log (100000000000 / 121485904637) := by
    rw [show ((121485904637 / 100000000000) : ℝ) = ((100000000000 / 121485904637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5987_neg : (97560353 / 500000000) ≤ -Real.log (500000000000 / 607728845703) ∧
    -Real.log (500000000000 / 607728845703) ≤ (195120707 / 1000000000) := by
  have h := checkLog_sound (w := (107728845703 / 1107728845703)) (n := 12)
    (lo := (97560353 / 500000000)) (hi := (195120707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607728845703 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607728845703 / 500000000000) = 1/(500000000000 / 607728845703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5987 : Bounds (97560353 / 500000000) (195120707 / 1000000000) (Real.log (607728845703 / 500000000000)) := by
  have h := reflection_log_5987_neg
  have he : Real.log (607728845703 / 500000000000) = -Real.log (500000000000 / 607728845703) := by
    rw [show ((607728845703 / 500000000000) : ℝ) = ((500000000000 / 607728845703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5988_neg : (390695019 / 1000000000) ≤ -Real.log (500000000000 / 739003840911) ∧
    -Real.log (500000000000 / 739003840911) ≤ (19534751 / 50000000) := by
  have h := checkLog_sound (w := (239003840911 / 1239003840911)) (n := 12)
    (lo := (390695019 / 1000000000)) (hi := (19534751 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739003840911 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739003840911 / 500000000000) = 1/(500000000000 / 739003840911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5988 : Bounds (390695019 / 1000000000) (19534751 / 50000000) (Real.log (739003840911 / 500000000000)) := by
  have h := reflection_log_5988_neg
  have he : Real.log (739003840911 / 500000000000) = -Real.log (500000000000 / 739003840911) := by
    rw [show ((739003840911 / 500000000000) : ℝ) = ((500000000000 / 739003840911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5989_neg : (390902753 / 1000000000) ≤ -Real.log (500000000000 / 739157372987) ∧
    -Real.log (500000000000 / 739157372987) ≤ (195451377 / 500000000) := by
  have h := checkLog_sound (w := (239157372987 / 1239157372987)) (n := 12)
    (lo := (390902753 / 1000000000)) (hi := (195451377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739157372987 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739157372987 / 500000000000) = 1/(500000000000 / 739157372987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5989 : Bounds (390902753 / 1000000000) (195451377 / 500000000) (Real.log (739157372987 / 500000000000)) := by
  have h := reflection_log_5989_neg
  have he : Real.log (739157372987 / 500000000000) = -Real.log (500000000000 / 739157372987) := by
    rw [show ((739157372987 / 500000000000) : ℝ) = ((500000000000 / 739157372987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5990_neg : (176554961 / 1000000000) ≤ -Real.log (10000 / 11931) ∧
    -Real.log (10000 / 11931) ≤ (88277481 / 500000000) := by
  have h := checkLog_sound (w := (1931 / 21931)) (n := 12)
    (lo := (176554961 / 1000000000)) (hi := (88277481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11931 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11931 / 10000) = 1/(10000 / 11931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5990 : Bounds (176554961 / 1000000000) (88277481 / 500000000) (Real.log (11931 / 10000)) := by
  have h := reflection_log_5990_neg
  have he : Real.log (11931 / 10000) = -Real.log (10000 / 11931) := by
    rw [show ((11931 / 10000) : ℝ) = ((10000 / 11931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5991_neg : (107277767 / 500000000) ≤ -Real.log (8069 / 10000) ∧
    -Real.log (8069 / 10000) ≤ (42911107 / 200000000) := by
  have h := checkLog_sound (w := (1931 / 18069)) (n := 12)
    (lo := (107277767 / 500000000)) (hi := (42911107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8069) = 1/(8069 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5991 : Bounds (-42911107 / 200000000) (-107277767 / 500000000) (Real.log (8069 / 10000)) := by
  have h := reflection_log_5991_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5992_neg : (193081 / 1000000000) ≤ -Real.log (10000000 / 10001931) ∧
    -Real.log (10000000 / 10001931) ≤ (96541 / 500000000) := by
  have h := checkLog_sound (w := (1931 / 20001931)) (n := 12)
    (lo := (193081 / 1000000000)) (hi := (96541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001931 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001931 / 10000000) = 1/(10000000 / 10001931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5992 : Bounds (193081 / 1000000000) (96541 / 500000000) (Real.log (10001931 / 10000000)) := by
  have h := reflection_log_5992_neg
  have he : Real.log (10001931 / 10000000) = -Real.log (10000000 / 10001931) := by
    rw [show ((10001931 / 10000000) : ℝ) = ((10000000 / 10001931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5993_neg : (96559 / 500000000) ≤ -Real.log (9998069 / 10000000) ∧
    -Real.log (9998069 / 10000000) ≤ (193119 / 1000000000) := by
  have h := checkLog_sound (w := (1931 / 19998069)) (n := 12)
    (lo := (96559 / 500000000)) (hi := (193119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998069) = 1/(9998069 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5993 : Bounds (-193119 / 1000000000) (-96559 / 500000000) (Real.log (9998069 / 10000000)) := by
  have h := reflection_log_5993_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5994_neg : (46316481 / 500000000) ≤ -Real.log (1000000 / 1097059) ∧
    -Real.log (1000000 / 1097059) ≤ (92632963 / 1000000000) := by
  have h := checkLog_sound (w := (97059 / 2097059)) (n := 12)
    (lo := (46316481 / 500000000)) (hi := (92632963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097059 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097059 / 1000000) = 1/(1000000 / 1097059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5994 : Bounds (46316481 / 500000000) (92632963 / 1000000000) (Real.log (1097059 / 1000000)) := by
  have h := reflection_log_5994_neg
  have he : Real.log (1097059 / 1000000) = -Real.log (1000000 / 1097059) := by
    rw [show ((1097059 / 1000000) : ℝ) = ((1000000 / 1097059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5995_neg : (20419613 / 200000000) ≤ -Real.log (902941 / 1000000) ∧
    -Real.log (902941 / 1000000) ≤ (51049033 / 500000000) := by
  have h := checkLog_sound (w := (97059 / 1902941)) (n := 12)
    (lo := (20419613 / 200000000)) (hi := (51049033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902941) = 1/(902941 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5995 : Bounds (-51049033 / 500000000) (-20419613 / 200000000) (Real.log (902941 / 1000000)) := by
  have h := reflection_log_5995_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5996_neg : (1857107 / 20000000) ≤ -Real.log (1000000 / 1097303) ∧
    -Real.log (1000000 / 1097303) ≤ (92855351 / 1000000000) := by
  have h := checkLog_sound (w := (97303 / 2097303)) (n := 12)
    (lo := (1857107 / 20000000)) (hi := (92855351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097303 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097303 / 1000000) = 1/(1000000 / 1097303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5996 : Bounds (1857107 / 20000000) (92855351 / 1000000000) (Real.log (1097303 / 1000000)) := by
  have h := reflection_log_5996_neg
  have he : Real.log (1097303 / 1000000) = -Real.log (1000000 / 1097303) := by
    rw [show ((1097303 / 1000000) : ℝ) = ((1000000 / 1097303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5997_neg : (10236833 / 100000000) ≤ -Real.log (902697 / 1000000) ∧
    -Real.log (902697 / 1000000) ≤ (102368331 / 1000000000) := by
  have h := checkLog_sound (w := (97303 / 1902697)) (n := 12)
    (lo := (10236833 / 100000000)) (hi := (102368331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902697) = 1/(902697 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5997 : Bounds (-102368331 / 1000000000) (-10236833 / 100000000) (Real.log (902697 / 1000000)) := by
  have h := reflection_log_5997_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5998_neg : (9512979 / 1000000000) ≤ -Real.log (990532126191 / 1000000000000) ∧
    -Real.log (990532126191 / 1000000000000) ≤ (475649 / 50000000) := by
  have h := checkLog_sound (w := (9467873809 / 1990532126191)) (n := 12)
    (lo := (9512979 / 1000000000)) (hi := (475649 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990532126191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990532126191) = 1/(990532126191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5998 : Bounds (-475649 / 50000000) (-9512979 / 1000000000) (Real.log (990532126191 / 1000000000000)) := by
  have h := reflection_log_5998_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5999_neg : (4732551 / 500000000) ≤ -Real.log (990579550519 / 1000000000000) ∧
    -Real.log (990579550519 / 1000000000000) ≤ (9465103 / 1000000000) := by
  have h := checkLog_sound (w := (9420449481 / 1990579550519)) (n := 12)
    (lo := (4732551 / 500000000)) (hi := (9465103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990579550519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990579550519) = 1/(990579550519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5999 : Bounds (-9465103 / 1000000000) (-4732551 / 500000000) (Real.log (990579550519 / 1000000000000)) := by
  have h := reflection_log_5999_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6000_neg : (48682757 / 250000000) ≤ -Real.log (800000000 / 971987317) ∧
    -Real.log (800000000 / 971987317) ≤ (194731029 / 1000000000) := by
  have h := checkLog_sound (w := (171987317 / 1771987317)) (n := 12)
    (lo := (48682757 / 250000000)) (hi := (194731029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((971987317 / 800000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(971987317 / 800000000) = 1/(800000000 / 971987317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6000 : Bounds (48682757 / 250000000) (194731029 / 1000000000) (Real.log (971987317 / 800000000)) := by
  have h := reflection_log_6000_neg
  have he : Real.log (971987317 / 800000000) = -Real.log (800000000 / 971987317) := by
    rw [show ((971987317 / 800000000) : ℝ) = ((800000000 / 971987317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6001_neg : (195223681 / 1000000000) ≤ -Real.log (500000000000 / 607791429461) ∧
    -Real.log (500000000000 / 607791429461) ≤ (97611841 / 500000000) := by
  have h := checkLog_sound (w := (107791429461 / 1107791429461)) (n := 12)
    (lo := (195223681 / 1000000000)) (hi := (97611841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607791429461 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607791429461 / 500000000000) = 1/(500000000000 / 607791429461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6001 : Bounds (195223681 / 1000000000) (97611841 / 500000000) (Real.log (607791429461 / 500000000000)) := by
  have h := reflection_log_6001_neg
  have he : Real.log (607791429461 / 500000000000) = -Real.log (500000000000 / 607791429461) := by
    rw [show ((607791429461 / 500000000000) : ℝ) = ((500000000000 / 607791429461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6002_neg : (390902753 / 1000000000) ≤ -Real.log (250000000000 / 369578686493) ∧
    -Real.log (250000000000 / 369578686493) ≤ (195451377 / 500000000) := by
  have h := checkLog_sound (w := (119578686493 / 619578686493)) (n := 12)
    (lo := (390902753 / 1000000000)) (hi := (195451377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369578686493 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369578686493 / 250000000000) = 1/(250000000000 / 369578686493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6002 : Bounds (390902753 / 1000000000) (195451377 / 500000000) (Real.log (369578686493 / 250000000000)) := by
  have h := reflection_log_6002_neg
  have he : Real.log (369578686493 / 250000000000) = -Real.log (250000000000 / 369578686493) := by
    rw [show ((369578686493 / 250000000000) : ℝ) = ((250000000000 / 369578686493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6003_neg : (12222203 / 31250000) ≤ -Real.log (125000000000 / 184827735779) ∧
    -Real.log (125000000000 / 184827735779) ≤ (391110497 / 1000000000) := by
  have h := checkLog_sound (w := (59827735779 / 309827735779)) (n := 12)
    (lo := (12222203 / 31250000)) (hi := (391110497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184827735779 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184827735779 / 125000000000) = 1/(125000000000 / 184827735779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6003 : Bounds (12222203 / 31250000) (391110497 / 1000000000) (Real.log (184827735779 / 125000000000)) := by
  have h := reflection_log_6003_neg
  have he : Real.log (184827735779 / 125000000000) = -Real.log (125000000000 / 184827735779) := by
    rw [show ((184827735779 / 125000000000) : ℝ) = ((125000000000 / 184827735779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6004_neg : (176638773 / 1000000000) ≤ -Real.log (2500 / 2983) ∧
    -Real.log (2500 / 2983) ≤ (88319387 / 500000000) := by
  have h := checkLog_sound (w := (483 / 5483)) (n := 12)
    (lo := (176638773 / 1000000000)) (hi := (88319387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2983 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2983 / 2500) = 1/(2500 / 2983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6004 : Bounds (176638773 / 1000000000) (88319387 / 500000000) (Real.log (2983 / 2500)) := by
  have h := reflection_log_6004_neg
  have he : Real.log (2983 / 2500) = -Real.log (2500 / 2983) := by
    rw [show ((2983 / 2500) : ℝ) = ((2500 / 2983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6005_neg : (13417467 / 62500000) ≤ -Real.log (2017 / 2500) ∧
    -Real.log (2017 / 2500) ≤ (214679473 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 4517)) (n := 12)
    (lo := (13417467 / 62500000)) (hi := (214679473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2017) = 1/(2017 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6005 : Bounds (-214679473 / 1000000000) (-13417467 / 62500000) (Real.log (2017 / 2500)) := by
  have h := reflection_log_6005_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6006_neg : (193181 / 1000000000) ≤ -Real.log (2500000 / 2500483) ∧
    -Real.log (2500000 / 2500483) ≤ (96591 / 500000000) := by
  have h := checkLog_sound (w := (483 / 5000483)) (n := 12)
    (lo := (193181 / 1000000000)) (hi := (96591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500483 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500483 / 2500000) = 1/(2500000 / 2500483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6006 : Bounds (193181 / 1000000000) (96591 / 500000000) (Real.log (2500483 / 2500000)) := by
  have h := reflection_log_6006_neg
  have he : Real.log (2500483 / 2500000) = -Real.log (2500000 / 2500483) := by
    rw [show ((2500483 / 2500000) : ℝ) = ((2500000 / 2500483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6007_neg : (96609 / 500000000) ≤ -Real.log (2499517 / 2500000) ∧
    -Real.log (2499517 / 2500000) ≤ (193219 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 4999517)) (n := 12)
    (lo := (96609 / 500000000)) (hi := (193219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499517) = 1/(2499517 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6007 : Bounds (-193219 / 1000000000) (-96609 / 500000000) (Real.log (2499517 / 2500000)) := by
  have h := reflection_log_6007_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6008_neg : (92679449 / 1000000000) ≤ -Real.log (100000 / 109711) ∧
    -Real.log (100000 / 109711) ≤ (1853589 / 20000000) := by
  have h := checkLog_sound (w := (9711 / 209711)) (n := 12)
    (lo := (92679449 / 1000000000)) (hi := (1853589 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109711 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109711 / 100000) = 1/(100000 / 109711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6008 : Bounds (92679449 / 1000000000) (1853589 / 20000000) (Real.log (109711 / 100000)) := by
  have h := reflection_log_6008_neg
  have he : Real.log (109711 / 100000) = -Real.log (100000 / 109711) := by
    rw [show ((109711 / 100000) : ℝ) = ((100000 / 109711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6009_neg : (102154549 / 1000000000) ≤ -Real.log (90289 / 100000) ∧
    -Real.log (90289 / 100000) ≤ (2043091 / 20000000) := by
  have h := checkLog_sound (w := (9711 / 190289)) (n := 12)
    (lo := (102154549 / 1000000000)) (hi := (2043091 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90289) = 1/(90289 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6009 : Bounds (-2043091 / 20000000) (-102154549 / 1000000000) (Real.log (90289 / 100000)) := by
  have h := reflection_log_6009_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6010_neg : (92901827 / 1000000000) ≤ -Real.log (500000 / 548677) ∧
    -Real.log (500000 / 548677) ≤ (23225457 / 250000000) := by
  have h := checkLog_sound (w := (48677 / 1048677)) (n := 12)
    (lo := (92901827 / 1000000000)) (hi := (23225457 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548677 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548677 / 500000) = 1/(500000 / 548677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6010 : Bounds (92901827 / 1000000000) (23225457 / 250000000) (Real.log (548677 / 500000)) := by
  have h := reflection_log_6010_neg
  have he : Real.log (548677 / 500000) = -Real.log (500000 / 548677) := by
    rw [show ((548677 / 500000) : ℝ) = ((500000 / 548677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6011_neg : (102424829 / 1000000000) ≤ -Real.log (451323 / 500000) ∧
    -Real.log (451323 / 500000) ≤ (10242483 / 100000000) := by
  have h := checkLog_sound (w := (48677 / 951323)) (n := 12)
    (lo := (102424829 / 1000000000)) (hi := (10242483 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451323) = 1/(451323 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6011 : Bounds (-10242483 / 100000000) (-102424829 / 1000000000) (Real.log (451323 / 500000)) := by
  have h := reflection_log_6011_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6012_neg : (9523001 / 1000000000) ≤ -Real.log (247630549671 / 250000000000) ∧
    -Real.log (247630549671 / 250000000000) ≤ (4761501 / 500000000) := by
  have h := checkLog_sound (w := (2369450329 / 497630549671)) (n := 12)
    (lo := (9523001 / 1000000000)) (hi := (4761501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247630549671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247630549671) = 1/(247630549671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6012 : Bounds (-4761501 / 500000000) (-9523001 / 1000000000) (Real.log (247630549671 / 250000000000)) := by
  have h := reflection_log_6012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6013_neg : (9475099 / 1000000000) ≤ -Real.log (9905696479 / 10000000000) ∧
    -Real.log (9905696479 / 10000000000) ≤ (94751 / 10000000) := by
  have h := checkLog_sound (w := (94303521 / 19905696479)) (n := 12)
    (lo := (9475099 / 1000000000)) (hi := (94751 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9905696479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9905696479) = 1/(9905696479 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6013 : Bounds (-94751 / 10000000) (-9475099 / 1000000000) (Real.log (9905696479 / 10000000000)) := by
  have h := reflection_log_6013_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6014_neg : (97416999 / 500000000) ≤ -Real.log (125000000000 / 151888657533) ∧
    -Real.log (125000000000 / 151888657533) ≤ (194833999 / 1000000000) := by
  have h := checkLog_sound (w := (26888657533 / 276888657533)) (n := 12)
    (lo := (97416999 / 500000000)) (hi := (194833999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151888657533 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151888657533 / 125000000000) = 1/(125000000000 / 151888657533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6014 : Bounds (97416999 / 500000000) (194833999 / 1000000000) (Real.log (151888657533 / 125000000000)) := by
  have h := reflection_log_6014_neg
  have he : Real.log (151888657533 / 125000000000) = -Real.log (125000000000 / 151888657533) := by
    rw [show ((151888657533 / 125000000000) : ℝ) = ((125000000000 / 151888657533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6015_neg : (3051979 / 15625000) ≤ -Real.log (125000000000 / 151963505073) ∧
    -Real.log (125000000000 / 151963505073) ≤ (195326657 / 1000000000) := by
  have h := checkLog_sound (w := (26963505073 / 276963505073)) (n := 12)
    (lo := (3051979 / 15625000)) (hi := (195326657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151963505073 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151963505073 / 125000000000) = 1/(125000000000 / 151963505073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6015 : Bounds (3051979 / 15625000) (195326657 / 1000000000) (Real.log (151963505073 / 125000000000)) := by
  have h := reflection_log_6015_neg
  have he : Real.log (151963505073 / 125000000000) = -Real.log (125000000000 / 151963505073) := by
    rw [show ((151963505073 / 125000000000) : ℝ) = ((125000000000 / 151963505073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
