import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4160_neg : (11251 / 62500000) ≤ -Real.log (49991 / 50000) ∧
    -Real.log (49991 / 50000) ≤ (180017 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 99991)) (n := 12)
    (lo := (11251 / 62500000)) (hi := (180017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49991) = 1/(49991 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4160 : Bounds (-180017 / 1000000000) (-11251 / 62500000) (Real.log (49991 / 50000)) := by
  have h := reflection_log_4160_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4161_neg : (8653543 / 100000000) ≤ -Real.log (100000 / 109039) ∧
    -Real.log (100000 / 109039) ≤ (86535431 / 1000000000) := by
  have h := checkLog_sound (w := (9039 / 209039)) (n := 12)
    (lo := (8653543 / 100000000)) (hi := (86535431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109039 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109039 / 100000) = 1/(100000 / 109039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4161 : Bounds (8653543 / 100000000) (86535431 / 1000000000) (Real.log (109039 / 100000)) := by
  have h := reflection_log_4161_neg
  have he : Real.log (109039 / 100000) = -Real.log (100000 / 109039) := by
    rw [show ((109039 / 100000) : ℝ) = ((100000 / 109039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4162_neg : (47369671 / 500000000) ≤ -Real.log (90961 / 100000) ∧
    -Real.log (90961 / 100000) ≤ (94739343 / 1000000000) := by
  have h := checkLog_sound (w := (9039 / 190961)) (n := 12)
    (lo := (47369671 / 500000000)) (hi := (94739343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90961) = 1/(90961 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4162 : Bounds (-94739343 / 1000000000) (-47369671 / 500000000) (Real.log (90961 / 100000)) := by
  have h := reflection_log_4162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4163_neg : (43373629 / 500000000) ≤ -Real.log (1000000 / 1090621) ∧
    -Real.log (1000000 / 1090621) ≤ (86747259 / 1000000000) := by
  have h := checkLog_sound (w := (90621 / 2090621)) (n := 12)
    (lo := (43373629 / 500000000)) (hi := (86747259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090621 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090621 / 1000000) = 1/(1000000 / 1090621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4163 : Bounds (43373629 / 500000000) (86747259 / 1000000000) (Real.log (1090621 / 1000000)) := by
  have h := reflection_log_4163_neg
  have he : Real.log (1090621 / 1000000) = -Real.log (1000000 / 1090621) := by
    rw [show ((1090621 / 1000000) : ℝ) = ((1000000 / 1090621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4164_neg : (9499333 / 100000000) ≤ -Real.log (909379 / 1000000) ∧
    -Real.log (909379 / 1000000) ≤ (94993331 / 1000000000) := by
  have h := checkLog_sound (w := (90621 / 1909379)) (n := 12)
    (lo := (9499333 / 100000000)) (hi := (94993331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909379) = 1/(909379 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4164 : Bounds (-94993331 / 1000000000) (-9499333 / 100000000) (Real.log (909379 / 1000000)) := by
  have h := reflection_log_4164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4165_neg : (8246071 / 1000000000) ≤ -Real.log (991787834359 / 1000000000000) ∧
    -Real.log (991787834359 / 1000000000000) ≤ (1030759 / 125000000) := by
  have h := checkLog_sound (w := (8212165641 / 1991787834359)) (n := 12)
    (lo := (8246071 / 1000000000)) (hi := (1030759 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991787834359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991787834359) = 1/(991787834359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4165 : Bounds (-1030759 / 125000000) (-8246071 / 1000000000) (Real.log (991787834359 / 1000000000000)) := by
  have h := reflection_log_4165_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4166_neg : (1025489 / 125000000) ≤ -Real.log (9918296479 / 10000000000) ∧
    -Real.log (9918296479 / 10000000000) ≤ (8203913 / 1000000000) := by
  have h := checkLog_sound (w := (81703521 / 19918296479)) (n := 12)
    (lo := (1025489 / 125000000)) (hi := (8203913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9918296479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9918296479) = 1/(9918296479 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4166 : Bounds (-8203913 / 1000000000) (-1025489 / 125000000) (Real.log (9918296479 / 10000000000)) := by
  have h := reflection_log_4166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4167_neg : (181274773 / 1000000000) ≤ -Real.log (12500000000 / 14984306461) ∧
    -Real.log (12500000000 / 14984306461) ≤ (90637387 / 500000000) := by
  have h := checkLog_sound (w := (2484306461 / 27484306461)) (n := 12)
    (lo := (181274773 / 1000000000)) (hi := (90637387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14984306461 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14984306461 / 12500000000) = 1/(12500000000 / 14984306461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4167 : Bounds (181274773 / 1000000000) (90637387 / 500000000) (Real.log (14984306461 / 12500000000)) := by
  have h := reflection_log_4167_neg
  have he : Real.log (14984306461 / 12500000000) = -Real.log (12500000000 / 14984306461) := by
    rw [show ((14984306461 / 12500000000) : ℝ) = ((12500000000 / 14984306461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4168_neg : (45435147 / 250000000) ≤ -Real.log (250000000000 / 299825760217) ∧
    -Real.log (250000000000 / 299825760217) ≤ (181740589 / 1000000000) := by
  have h := checkLog_sound (w := (49825760217 / 549825760217)) (n := 12)
    (lo := (45435147 / 250000000)) (hi := (181740589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299825760217 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299825760217 / 250000000000) = 1/(250000000000 / 299825760217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4168 : Bounds (45435147 / 250000000) (181740589 / 1000000000) (Real.log (299825760217 / 250000000000)) := by
  have h := reflection_log_4168_neg
  have he : Real.log (299825760217 / 250000000000) = -Real.log (250000000000 / 299825760217) := by
    rw [show ((299825760217 / 250000000000) : ℝ) = ((250000000000 / 299825760217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4169_neg : (90939671 / 250000000) ≤ -Real.log (500000000000 / 719363492257) ∧
    -Real.log (500000000000 / 719363492257) ≤ (72751737 / 200000000) := by
  have h := checkLog_sound (w := (219363492257 / 1219363492257)) (n := 12)
    (lo := (90939671 / 250000000)) (hi := (72751737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719363492257 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719363492257 / 500000000000) = 1/(500000000000 / 719363492257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4169 : Bounds (90939671 / 250000000) (72751737 / 200000000) (Real.log (719363492257 / 500000000000)) := by
  have h := reflection_log_4169_neg
  have he : Real.log (719363492257 / 500000000000) = -Real.log (500000000000 / 719363492257) := by
    rw [show ((719363492257 / 500000000000) : ℝ) = ((500000000000 / 719363492257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4170_neg : (363965377 / 1000000000) ≤ -Real.log (250000000000 / 359756097561) ∧
    -Real.log (250000000000 / 359756097561) ≤ (181982689 / 500000000) := by
  have h := checkLog_sound (w := (109756097561 / 609756097561)) (n := 12)
    (lo := (363965377 / 1000000000)) (hi := (181982689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359756097561 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359756097561 / 250000000000) = 1/(250000000000 / 359756097561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4170 : Bounds (363965377 / 1000000000) (181982689 / 500000000) (Real.log (359756097561 / 250000000000)) := by
  have h := reflection_log_4170_neg
  have he : Real.log (359756097561 / 250000000000) = -Real.log (250000000000 / 359756097561) := by
    rw [show ((359756097561 / 250000000000) : ℝ) = ((250000000000 / 359756097561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4171_neg : (8279959 / 50000000) ≤ -Real.log (10000 / 11801) ∧
    -Real.log (10000 / 11801) ≤ (165599181 / 1000000000) := by
  have h := checkLog_sound (w := (1801 / 21801)) (n := 12)
    (lo := (8279959 / 50000000)) (hi := (165599181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11801 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11801 / 10000) = 1/(10000 / 11801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4171 : Bounds (8279959 / 50000000) (165599181 / 1000000000) (Real.log (11801 / 10000)) := by
  have h := reflection_log_4171_neg
  have he : Real.log (11801 / 10000) = -Real.log (10000 / 11801) := by
    rw [show ((11801 / 10000) : ℝ) = ((10000 / 11801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4172_neg : (198572897 / 1000000000) ≤ -Real.log (8199 / 10000) ∧
    -Real.log (8199 / 10000) ≤ (99286449 / 500000000) := by
  have h := checkLog_sound (w := (1801 / 18199)) (n := 12)
    (lo := (198572897 / 1000000000)) (hi := (99286449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8199) = 1/(8199 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4172 : Bounds (-99286449 / 500000000) (-198572897 / 1000000000) (Real.log (8199 / 10000)) := by
  have h := reflection_log_4172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4173_neg : (180083 / 1000000000) ≤ -Real.log (10000000 / 10001801) ∧
    -Real.log (10000000 / 10001801) ≤ (45021 / 250000000) := by
  have h := checkLog_sound (w := (1801 / 20001801)) (n := 12)
    (lo := (180083 / 1000000000)) (hi := (45021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001801 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001801 / 10000000) = 1/(10000000 / 10001801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4173 : Bounds (180083 / 1000000000) (45021 / 250000000) (Real.log (10001801 / 10000000)) := by
  have h := reflection_log_4173_neg
  have he : Real.log (10001801 / 10000000) = -Real.log (10000000 / 10001801) := by
    rw [show ((10001801 / 10000000) : ℝ) = ((10000000 / 10001801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4174_neg : (45029 / 250000000) ≤ -Real.log (9998199 / 10000000) ∧
    -Real.log (9998199 / 10000000) ≤ (180117 / 1000000000) := by
  have h := checkLog_sound (w := (1801 / 19998199)) (n := 12)
    (lo := (45029 / 250000000)) (hi := (180117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998199) = 1/(9998199 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4174 : Bounds (-180117 / 1000000000) (-45029 / 250000000) (Real.log (9998199 / 10000000)) := by
  have h := reflection_log_4174_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4175_neg : (86582201 / 1000000000) ≤ -Real.log (1000000 / 1090441) ∧
    -Real.log (1000000 / 1090441) ≤ (43291101 / 500000000) := by
  have h := checkLog_sound (w := (90441 / 2090441)) (n := 12)
    (lo := (86582201 / 1000000000)) (hi := (43291101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090441 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090441 / 1000000) = 1/(1000000 / 1090441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4175 : Bounds (86582201 / 1000000000) (43291101 / 500000000) (Real.log (1090441 / 1000000)) := by
  have h := reflection_log_4175_neg
  have he : Real.log (1090441 / 1000000) = -Real.log (1000000 / 1090441) := by
    rw [show ((1090441 / 1000000) : ℝ) = ((1000000 / 1090441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4176_neg : (23698853 / 250000000) ≤ -Real.log (909559 / 1000000) ∧
    -Real.log (909559 / 1000000) ≤ (94795413 / 1000000000) := by
  have h := checkLog_sound (w := (90441 / 1909559)) (n := 12)
    (lo := (23698853 / 250000000)) (hi := (94795413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909559) = 1/(909559 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4176 : Bounds (-94795413 / 1000000000) (-23698853 / 250000000) (Real.log (909559 / 1000000)) := by
  have h := reflection_log_4176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4177_neg : (4339701 / 50000000) ≤ -Real.log (62500 / 68167) ∧
    -Real.log (62500 / 68167) ≤ (86794021 / 1000000000) := by
  have h := checkLog_sound (w := (5667 / 130667)) (n := 12)
    (lo := (4339701 / 50000000)) (hi := (86794021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68167 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68167 / 62500) = 1/(62500 / 68167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4177 : Bounds (4339701 / 50000000) (86794021 / 1000000000) (Real.log (68167 / 62500)) := by
  have h := reflection_log_4177_neg
  have he : Real.log (68167 / 62500) = -Real.log (62500 / 68167) := by
    rw [show ((68167 / 62500) : ℝ) = ((62500 / 68167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4178_neg : (95049413 / 1000000000) ≤ -Real.log (56833 / 62500) ∧
    -Real.log (56833 / 62500) ≤ (47524707 / 500000000) := by
  have h := checkLog_sound (w := (5667 / 119333)) (n := 12)
    (lo := (95049413 / 1000000000)) (hi := (47524707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56833) = 1/(56833 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4178 : Bounds (-47524707 / 500000000) (-95049413 / 1000000000) (Real.log (56833 / 62500)) := by
  have h := reflection_log_4178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4179_neg : (8255393 / 1000000000) ≤ -Real.log (3874135111 / 3906250000) ∧
    -Real.log (3874135111 / 3906250000) ≤ (4127697 / 500000000) := by
  have h := checkLog_sound (w := (32114889 / 7780385111)) (n := 12)
    (lo := (8255393 / 1000000000)) (hi := (4127697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3874135111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3874135111) = 1/(3874135111 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4179 : Bounds (-4127697 / 500000000) (-8255393 / 1000000000) (Real.log (3874135111 / 3906250000)) := by
  have h := reflection_log_4179_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4180_neg : (821321 / 100000000) ≤ -Real.log (991820425519 / 1000000000000) ∧
    -Real.log (991820425519 / 1000000000000) ≤ (8213211 / 1000000000) := by
  have h := checkLog_sound (w := (8179574481 / 1991820425519)) (n := 12)
    (lo := (821321 / 100000000)) (hi := (8213211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991820425519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991820425519) = 1/(991820425519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4180 : Bounds (-8213211 / 1000000000) (-821321 / 100000000) (Real.log (991820425519 / 1000000000000)) := by
  have h := reflection_log_4180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4181_neg : (181377613 / 1000000000) ≤ -Real.log (125000000000 / 149858475371) ∧
    -Real.log (125000000000 / 149858475371) ≤ (90688807 / 500000000) := by
  have h := checkLog_sound (w := (24858475371 / 274858475371)) (n := 12)
    (lo := (181377613 / 1000000000)) (hi := (90688807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149858475371 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149858475371 / 125000000000) = 1/(125000000000 / 149858475371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4181 : Bounds (181377613 / 1000000000) (90688807 / 500000000) (Real.log (149858475371 / 125000000000)) := by
  have h := reflection_log_4181_neg
  have he : Real.log (149858475371 / 125000000000) = -Real.log (125000000000 / 149858475371) := by
    rw [show ((149858475371 / 125000000000) : ℝ) = ((125000000000 / 149858475371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4182_neg : (181843433 / 1000000000) ≤ -Real.log (500000000000 / 599713194799) ∧
    -Real.log (500000000000 / 599713194799) ≤ (90921717 / 500000000) := by
  have h := checkLog_sound (w := (99713194799 / 1099713194799)) (n := 12)
    (lo := (181843433 / 1000000000)) (hi := (90921717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599713194799 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599713194799 / 500000000000) = 1/(500000000000 / 599713194799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4182 : Bounds (181843433 / 1000000000) (90921717 / 500000000) (Real.log (599713194799 / 500000000000)) := by
  have h := reflection_log_4182_neg
  have he : Real.log (599713194799 / 500000000000) = -Real.log (500000000000 / 599713194799) := by
    rw [show ((599713194799 / 500000000000) : ℝ) = ((500000000000 / 599713194799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4183_neg : (363965377 / 1000000000) ≤ -Real.log (500000000000 / 719512195121) ∧
    -Real.log (500000000000 / 719512195121) ≤ (181982689 / 500000000) := by
  have h := checkLog_sound (w := (219512195121 / 1219512195121)) (n := 12)
    (lo := (363965377 / 1000000000)) (hi := (181982689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719512195121 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719512195121 / 500000000000) = 1/(500000000000 / 719512195121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4183 : Bounds (363965377 / 1000000000) (181982689 / 500000000) (Real.log (719512195121 / 500000000000)) := by
  have h := reflection_log_4183_neg
  have he : Real.log (719512195121 / 500000000000) = -Real.log (500000000000 / 719512195121) := by
    rw [show ((719512195121 / 500000000000) : ℝ) = ((500000000000 / 719512195121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4184_neg : (182086039 / 500000000) ≤ -Real.log (500000000000 / 719660934261) ∧
    -Real.log (500000000000 / 719660934261) ≤ (364172079 / 1000000000) := by
  have h := checkLog_sound (w := (219660934261 / 1219660934261)) (n := 12)
    (lo := (182086039 / 500000000)) (hi := (364172079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719660934261 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719660934261 / 500000000000) = 1/(500000000000 / 719660934261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4184 : Bounds (182086039 / 500000000) (364172079 / 1000000000) (Real.log (719660934261 / 500000000000)) := by
  have h := reflection_log_4184_neg
  have he : Real.log (719660934261 / 500000000000) = -Real.log (500000000000 / 719660934261) := by
    rw [show ((719660934261 / 500000000000) : ℝ) = ((500000000000 / 719660934261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4185_neg : (33136783 / 200000000) ≤ -Real.log (5000 / 5901) ∧
    -Real.log (5000 / 5901) ≤ (41420979 / 250000000) := by
  have h := checkLog_sound (w := (901 / 10901)) (n := 12)
    (lo := (33136783 / 200000000)) (hi := (41420979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5901 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5901 / 5000) = 1/(5000 / 5901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4185 : Bounds (33136783 / 200000000) (41420979 / 250000000) (Real.log (5901 / 5000)) := by
  have h := reflection_log_4185_neg
  have he : Real.log (5901 / 5000) = -Real.log (5000 / 5901) := by
    rw [show ((5901 / 5000) : ℝ) = ((5000 / 5901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4186_neg : (19869487 / 100000000) ≤ -Real.log (4099 / 5000) ∧
    -Real.log (4099 / 5000) ≤ (198694871 / 1000000000) := by
  have h := checkLog_sound (w := (901 / 9099)) (n := 12)
    (lo := (19869487 / 100000000)) (hi := (198694871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4099) = 1/(4099 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4186 : Bounds (-198694871 / 1000000000) (-19869487 / 100000000) (Real.log (4099 / 5000)) := by
  have h := reflection_log_4186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4187_neg : (180183 / 1000000000) ≤ -Real.log (5000000 / 5000901) ∧
    -Real.log (5000000 / 5000901) ≤ (22523 / 125000000) := by
  have h := checkLog_sound (w := (901 / 10000901)) (n := 12)
    (lo := (180183 / 1000000000)) (hi := (22523 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000901 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000901 / 5000000) = 1/(5000000 / 5000901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4187 : Bounds (180183 / 1000000000) (22523 / 125000000) (Real.log (5000901 / 5000000)) := by
  have h := reflection_log_4187_neg
  have he : Real.log (5000901 / 5000000) = -Real.log (5000000 / 5000901) := by
    rw [show ((5000901 / 5000000) : ℝ) = ((5000000 / 5000901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4188_neg : (22527 / 125000000) ≤ -Real.log (4999099 / 5000000) ∧
    -Real.log (4999099 / 5000000) ≤ (180217 / 1000000000) := by
  have h := checkLog_sound (w := (901 / 9999099)) (n := 12)
    (lo := (22527 / 125000000)) (hi := (180217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999099) = 1/(4999099 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4188 : Bounds (-180217 / 1000000000) (-22527 / 125000000) (Real.log (4999099 / 5000000)) := by
  have h := reflection_log_4188_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4189_neg : (8662897 / 100000000) ≤ -Real.log (250000 / 272623) ∧
    -Real.log (250000 / 272623) ≤ (86628971 / 1000000000) := by
  have h := checkLog_sound (w := (22623 / 522623)) (n := 12)
    (lo := (8662897 / 100000000)) (hi := (86628971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272623 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272623 / 250000) = 1/(250000 / 272623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4189 : Bounds (8662897 / 100000000) (86628971 / 1000000000) (Real.log (272623 / 250000)) := by
  have h := reflection_log_4189_neg
  have he : Real.log (272623 / 250000) = -Real.log (250000 / 272623) := by
    rw [show ((272623 / 250000) : ℝ) = ((250000 / 272623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4190_neg : (18970297 / 200000000) ≤ -Real.log (227377 / 250000) ∧
    -Real.log (227377 / 250000) ≤ (47425743 / 500000000) := by
  have h := checkLog_sound (w := (22623 / 477377)) (n := 12)
    (lo := (18970297 / 200000000)) (hi := (47425743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227377) = 1/(227377 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4190 : Bounds (-47425743 / 500000000) (-18970297 / 200000000) (Real.log (227377 / 250000)) := by
  have h := reflection_log_4190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4191_neg : (86840779 / 1000000000) ≤ -Real.log (1000000 / 1090723) ∧
    -Real.log (1000000 / 1090723) ≤ (4342039 / 50000000) := by
  have h := checkLog_sound (w := (90723 / 2090723)) (n := 12)
    (lo := (86840779 / 1000000000)) (hi := (4342039 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090723 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090723 / 1000000) = 1/(1000000 / 1090723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4191 : Bounds (86840779 / 1000000000) (4342039 / 50000000) (Real.log (1090723 / 1000000)) := by
  have h := reflection_log_4191_neg
  have he : Real.log (1090723 / 1000000) = -Real.log (1000000 / 1090723) := by
    rw [show ((1090723 / 1000000) : ℝ) = ((1000000 / 1090723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4192_neg : (190211 / 2000000) ≤ -Real.log (909277 / 1000000) ∧
    -Real.log (909277 / 1000000) ≤ (95105501 / 1000000000) := by
  have h := checkLog_sound (w := (90723 / 1909277)) (n := 12)
    (lo := (190211 / 2000000)) (hi := (95105501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909277) = 1/(909277 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4192 : Bounds (-95105501 / 1000000000) (-190211 / 2000000) (Real.log (909277 / 1000000)) := by
  have h := reflection_log_4192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4193_neg : (8264721 / 1000000000) ≤ -Real.log (991769337271 / 1000000000000) ∧
    -Real.log (991769337271 / 1000000000000) ≤ (4132361 / 500000000) := by
  have h := checkLog_sound (w := (8230662729 / 1991769337271)) (n := 12)
    (lo := (8264721 / 1000000000)) (hi := (4132361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991769337271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991769337271) = 1/(991769337271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4193 : Bounds (-4132361 / 500000000) (-8264721 / 1000000000) (Real.log (991769337271 / 1000000000000)) := by
  have h := reflection_log_4193_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4194_neg : (4111257 / 500000000) ≤ -Real.log (61988199871 / 62500000000) ∧
    -Real.log (61988199871 / 62500000000) ≤ (1644503 / 200000000) := by
  have h := checkLog_sound (w := (511800129 / 124488199871)) (n := 12)
    (lo := (4111257 / 500000000)) (hi := (1644503 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61988199871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61988199871) = 1/(61988199871 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4194 : Bounds (-1644503 / 200000000) (-4111257 / 500000000) (Real.log (61988199871 / 62500000000)) := by
  have h := reflection_log_4194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4195_neg : (36296091 / 200000000) ≤ -Real.log (6250000000 / 7493694393) ∧
    -Real.log (6250000000 / 7493694393) ≤ (22685057 / 125000000) := by
  have h := checkLog_sound (w := (1243694393 / 13743694393)) (n := 12)
    (lo := (36296091 / 200000000)) (hi := (22685057 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7493694393 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7493694393 / 6250000000) = 1/(6250000000 / 7493694393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4195 : Bounds (36296091 / 200000000) (22685057 / 125000000) (Real.log (7493694393 / 6250000000)) := by
  have h := reflection_log_4195_neg
  have he : Real.log (7493694393 / 6250000000) = -Real.log (6250000000 / 7493694393) := by
    rw [show ((7493694393 / 6250000000) : ℝ) = ((6250000000 / 7493694393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4196_neg : (181946279 / 1000000000) ≤ -Real.log (500000000000 / 599774876083) ∧
    -Real.log (500000000000 / 599774876083) ≤ (4548657 / 25000000) := by
  have h := checkLog_sound (w := (99774876083 / 1099774876083)) (n := 12)
    (lo := (181946279 / 1000000000)) (hi := (4548657 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599774876083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599774876083 / 500000000000) = 1/(500000000000 / 599774876083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4196 : Bounds (181946279 / 1000000000) (4548657 / 25000000) (Real.log (599774876083 / 500000000000)) := by
  have h := reflection_log_4196_neg
  have he : Real.log (599774876083 / 500000000000) = -Real.log (500000000000 / 599774876083) := by
    rw [show ((599774876083 / 500000000000) : ℝ) = ((500000000000 / 599774876083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4197_neg : (182086039 / 500000000) ≤ -Real.log (25000000000 / 35983046713) ∧
    -Real.log (25000000000 / 35983046713) ≤ (364172079 / 1000000000) := by
  have h := checkLog_sound (w := (10983046713 / 60983046713)) (n := 12)
    (lo := (182086039 / 500000000)) (hi := (364172079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35983046713 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35983046713 / 25000000000) = 1/(25000000000 / 35983046713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4197 : Bounds (182086039 / 500000000) (364172079 / 1000000000) (Real.log (35983046713 / 25000000000)) := by
  have h := reflection_log_4197_neg
  have he : Real.log (35983046713 / 25000000000) = -Real.log (25000000000 / 35983046713) := by
    rw [show ((35983046713 / 25000000000) : ℝ) = ((25000000000 / 35983046713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4198_neg : (182189393 / 500000000) ≤ -Real.log (250000000000 / 359904854843) ∧
    -Real.log (250000000000 / 359904854843) ≤ (364378787 / 1000000000) := by
  have h := checkLog_sound (w := (109904854843 / 609904854843)) (n := 12)
    (lo := (182189393 / 500000000)) (hi := (364378787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359904854843 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359904854843 / 250000000000) = 1/(250000000000 / 359904854843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4198 : Bounds (182189393 / 500000000) (364378787 / 1000000000) (Real.log (359904854843 / 250000000000)) := by
  have h := reflection_log_4198_neg
  have he : Real.log (359904854843 / 250000000000) = -Real.log (250000000000 / 359904854843) := by
    rw [show ((359904854843 / 250000000000) : ℝ) = ((250000000000 / 359904854843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4199_neg : (165768643 / 1000000000) ≤ -Real.log (10000 / 11803) ∧
    -Real.log (10000 / 11803) ≤ (41442161 / 250000000) := by
  have h := checkLog_sound (w := (1803 / 21803)) (n := 12)
    (lo := (165768643 / 1000000000)) (hi := (41442161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11803 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11803 / 10000) = 1/(10000 / 11803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4199 : Bounds (165768643 / 1000000000) (41442161 / 250000000) (Real.log (11803 / 10000)) := by
  have h := reflection_log_4199_neg
  have he : Real.log (11803 / 10000) = -Real.log (10000 / 11803) := by
    rw [show ((11803 / 10000) : ℝ) = ((10000 / 11803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4200_neg : (198816859 / 1000000000) ≤ -Real.log (8197 / 10000) ∧
    -Real.log (8197 / 10000) ≤ (9940843 / 50000000) := by
  have h := checkLog_sound (w := (1803 / 18197)) (n := 12)
    (lo := (198816859 / 1000000000)) (hi := (9940843 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8197) = 1/(8197 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4200 : Bounds (-9940843 / 50000000) (-198816859 / 1000000000) (Real.log (8197 / 10000)) := by
  have h := reflection_log_4200_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4201_neg : (180283 / 1000000000) ≤ -Real.log (10000000 / 10001803) ∧
    -Real.log (10000000 / 10001803) ≤ (45071 / 250000000) := by
  have h := checkLog_sound (w := (1803 / 20001803)) (n := 12)
    (lo := (180283 / 1000000000)) (hi := (45071 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001803 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001803 / 10000000) = 1/(10000000 / 10001803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4201 : Bounds (180283 / 1000000000) (45071 / 250000000) (Real.log (10001803 / 10000000)) := by
  have h := reflection_log_4201_neg
  have he : Real.log (10001803 / 10000000) = -Real.log (10000000 / 10001803) := by
    rw [show ((10001803 / 10000000) : ℝ) = ((10000000 / 10001803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4202_neg : (45079 / 250000000) ≤ -Real.log (9998197 / 10000000) ∧
    -Real.log (9998197 / 10000000) ≤ (180317 / 1000000000) := by
  have h := checkLog_sound (w := (1803 / 19998197)) (n := 12)
    (lo := (45079 / 250000000)) (hi := (180317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998197) = 1/(9998197 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4202 : Bounds (-180317 / 1000000000) (-45079 / 250000000) (Real.log (9998197 / 10000000)) := by
  have h := reflection_log_4202_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4203_neg : (86675737 / 1000000000) ≤ -Real.log (1000000 / 1090543) ∧
    -Real.log (1000000 / 1090543) ≤ (43337869 / 500000000) := by
  have h := checkLog_sound (w := (90543 / 2090543)) (n := 12)
    (lo := (86675737 / 1000000000)) (hi := (43337869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090543 / 1000000) = 1/(1000000 / 1090543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4203 : Bounds (86675737 / 1000000000) (43337869 / 500000000) (Real.log (1090543 / 1000000)) := by
  have h := reflection_log_4203_neg
  have he : Real.log (1090543 / 1000000) = -Real.log (1000000 / 1090543) := by
    rw [show ((1090543 / 1000000) : ℝ) = ((1000000 / 1090543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4204_neg : (2372689 / 25000000) ≤ -Real.log (909457 / 1000000) ∧
    -Real.log (909457 / 1000000) ≤ (94907561 / 1000000000) := by
  have h := checkLog_sound (w := (90543 / 1909457)) (n := 12)
    (lo := (2372689 / 25000000)) (hi := (94907561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909457) = 1/(909457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4204 : Bounds (-94907561 / 1000000000) (-2372689 / 25000000) (Real.log (909457 / 1000000)) := by
  have h := reflection_log_4204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4205_neg : (17377507 / 200000000) ≤ -Real.log (500000 / 545387) ∧
    -Real.log (500000 / 545387) ≤ (5430471 / 62500000) := by
  have h := checkLog_sound (w := (45387 / 1045387)) (n := 12)
    (lo := (17377507 / 200000000)) (hi := (5430471 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545387 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545387 / 500000) = 1/(500000 / 545387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4205 : Bounds (17377507 / 200000000) (5430471 / 62500000) (Real.log (545387 / 500000)) := by
  have h := reflection_log_4205_neg
  have he : Real.log (545387 / 500000) = -Real.log (500000 / 545387) := by
    rw [show ((545387 / 500000) : ℝ) = ((500000 / 545387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4206_neg : (9516159 / 100000000) ≤ -Real.log (454613 / 500000) ∧
    -Real.log (454613 / 500000) ≤ (95161591 / 1000000000) := by
  have h := checkLog_sound (w := (45387 / 954613)) (n := 12)
    (lo := (9516159 / 100000000)) (hi := (95161591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454613) = 1/(454613 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4206 : Bounds (-95161591 / 1000000000) (-9516159 / 100000000) (Real.log (454613 / 500000)) := by
  have h := reflection_log_4206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4207_neg : (4137027 / 500000000) ≤ -Real.log (247940020231 / 250000000000) ∧
    -Real.log (247940020231 / 250000000000) ≤ (1654811 / 200000000) := by
  have h := checkLog_sound (w := (2059979769 / 497940020231)) (n := 12)
    (lo := (4137027 / 500000000)) (hi := (1654811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247940020231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247940020231) = 1/(247940020231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4207 : Bounds (-1654811 / 200000000) (-4137027 / 500000000) (Real.log (247940020231 / 250000000000)) := by
  have h := reflection_log_4207_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4208_neg : (8231823 / 1000000000) ≤ -Real.log (991801965151 / 1000000000000) ∧
    -Real.log (991801965151 / 1000000000000) ≤ (514489 / 62500000) := by
  have h := checkLog_sound (w := (8198034849 / 1991801965151)) (n := 12)
    (lo := (8231823 / 1000000000)) (hi := (514489 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991801965151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991801965151) = 1/(991801965151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4208 : Bounds (-514489 / 62500000) (-8231823 / 1000000000) (Real.log (991801965151 / 1000000000000)) := by
  have h := reflection_log_4208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4209_neg : (90791649 / 500000000) ≤ -Real.log (62500000000 / 74944651039) ∧
    -Real.log (62500000000 / 74944651039) ≤ (181583299 / 1000000000) := by
  have h := checkLog_sound (w := (12444651039 / 137444651039)) (n := 12)
    (lo := (90791649 / 500000000)) (hi := (181583299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74944651039 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74944651039 / 62500000000) = 1/(62500000000 / 74944651039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4209 : Bounds (90791649 / 500000000) (181583299 / 1000000000) (Real.log (74944651039 / 62500000000)) := by
  have h := reflection_log_4209_neg
  have he : Real.log (74944651039 / 62500000000) = -Real.log (62500000000 / 74944651039) := by
    rw [show ((74944651039 / 62500000000) : ℝ) = ((62500000000 / 74944651039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4210_neg : (91024563 / 500000000) ≤ -Real.log (500000000000 / 599836564287) ∧
    -Real.log (500000000000 / 599836564287) ≤ (182049127 / 1000000000) := by
  have h := checkLog_sound (w := (99836564287 / 1099836564287)) (n := 12)
    (lo := (91024563 / 500000000)) (hi := (182049127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599836564287 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599836564287 / 500000000000) = 1/(500000000000 / 599836564287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4210 : Bounds (91024563 / 500000000) (182049127 / 1000000000) (Real.log (599836564287 / 500000000000)) := by
  have h := reflection_log_4210_neg
  have he : Real.log (599836564287 / 500000000000) = -Real.log (500000000000 / 599836564287) := by
    rw [show ((599836564287 / 500000000000) : ℝ) = ((500000000000 / 599836564287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4211_neg : (182189393 / 500000000) ≤ -Real.log (100000000000 / 143961941937) ∧
    -Real.log (100000000000 / 143961941937) ≤ (364378787 / 1000000000) := by
  have h := checkLog_sound (w := (43961941937 / 243961941937)) (n := 12)
    (lo := (182189393 / 500000000)) (hi := (364378787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143961941937 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143961941937 / 100000000000) = 1/(100000000000 / 143961941937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4211 : Bounds (182189393 / 500000000) (364378787 / 1000000000) (Real.log (143961941937 / 100000000000)) := by
  have h := reflection_log_4211_neg
  have he : Real.log (143961941937 / 100000000000) = -Real.log (100000000000 / 143961941937) := by
    rw [show ((143961941937 / 100000000000) : ℝ) = ((100000000000 / 143961941937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4212_neg : (182292751 / 500000000) ≤ -Real.log (500000000000 / 719958521411) ∧
    -Real.log (500000000000 / 719958521411) ≤ (364585503 / 1000000000) := by
  have h := checkLog_sound (w := (219958521411 / 1219958521411)) (n := 12)
    (lo := (182292751 / 500000000)) (hi := (364585503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719958521411 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719958521411 / 500000000000) = 1/(500000000000 / 719958521411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4212 : Bounds (182292751 / 500000000) (364585503 / 1000000000) (Real.log (719958521411 / 500000000000)) := by
  have h := reflection_log_4212_neg
  have he : Real.log (719958521411 / 500000000000) = -Real.log (500000000000 / 719958521411) := by
    rw [show ((719958521411 / 500000000000) : ℝ) = ((500000000000 / 719958521411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4213_neg : (41463341 / 250000000) ≤ -Real.log (2500 / 2951) ∧
    -Real.log (2500 / 2951) ≤ (33170673 / 200000000) := by
  have h := checkLog_sound (w := (451 / 5451)) (n := 12)
    (lo := (41463341 / 250000000)) (hi := (33170673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2951 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2951 / 2500) = 1/(2500 / 2951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4213 : Bounds (41463341 / 250000000) (33170673 / 200000000) (Real.log (2951 / 2500)) := by
  have h := reflection_log_4213_neg
  have he : Real.log (2951 / 2500) = -Real.log (2500 / 2951) := by
    rw [show ((2951 / 2500) : ℝ) = ((2500 / 2951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4214_neg : (99469431 / 500000000) ≤ -Real.log (2049 / 2500) ∧
    -Real.log (2049 / 2500) ≤ (198938863 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 4549)) (n := 12)
    (lo := (99469431 / 500000000)) (hi := (198938863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2049) = 1/(2049 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4214 : Bounds (-198938863 / 1000000000) (-99469431 / 500000000) (Real.log (2049 / 2500)) := by
  have h := reflection_log_4214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4215_neg : (180383 / 1000000000) ≤ -Real.log (2500000 / 2500451) ∧
    -Real.log (2500000 / 2500451) ≤ (5637 / 31250000) := by
  have h := checkLog_sound (w := (451 / 5000451)) (n := 12)
    (lo := (180383 / 1000000000)) (hi := (5637 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500451 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500451 / 2500000) = 1/(2500000 / 2500451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4215 : Bounds (180383 / 1000000000) (5637 / 31250000) (Real.log (2500451 / 2500000)) := by
  have h := reflection_log_4215_neg
  have he : Real.log (2500451 / 2500000) = -Real.log (2500000 / 2500451) := by
    rw [show ((2500451 / 2500000) : ℝ) = ((2500000 / 2500451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4216_neg : (2819 / 15625000) ≤ -Real.log (2499549 / 2500000) ∧
    -Real.log (2499549 / 2500000) ≤ (180417 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 4999549)) (n := 12)
    (lo := (2819 / 15625000)) (hi := (180417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499549) = 1/(2499549 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4216 : Bounds (-180417 / 1000000000) (-2819 / 15625000) (Real.log (2499549 / 2500000)) := by
  have h := reflection_log_4216_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4217_neg : (17344317 / 200000000) ≤ -Real.log (1000000 / 1090593) ∧
    -Real.log (1000000 / 1090593) ≤ (43360793 / 500000000) := by
  have h := checkLog_sound (w := (90593 / 2090593)) (n := 12)
    (lo := (17344317 / 200000000)) (hi := (43360793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090593 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090593 / 1000000) = 1/(1000000 / 1090593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4217 : Bounds (17344317 / 200000000) (43360793 / 500000000) (Real.log (1090593 / 1000000)) := by
  have h := reflection_log_4217_neg
  have he : Real.log (1090593 / 1000000) = -Real.log (1000000 / 1090593) := by
    rw [show ((1090593 / 1000000) : ℝ) = ((1000000 / 1090593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4218_neg : (4748127 / 50000000) ≤ -Real.log (909407 / 1000000) ∧
    -Real.log (909407 / 1000000) ≤ (94962541 / 1000000000) := by
  have h := checkLog_sound (w := (90593 / 1909407)) (n := 12)
    (lo := (4748127 / 50000000)) (hi := (94962541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909407) = 1/(909407 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4218 : Bounds (-94962541 / 1000000000) (-4748127 / 50000000) (Real.log (909407 / 1000000)) := by
  have h := reflection_log_4218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4219_neg : (8693429 / 100000000) ≤ -Real.log (40000 / 43633) ∧
    -Real.log (40000 / 43633) ≤ (86934291 / 1000000000) := by
  have h := checkLog_sound (w := (3633 / 83633)) (n := 12)
    (lo := (8693429 / 100000000)) (hi := (86934291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43633 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43633 / 40000) = 1/(40000 / 43633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4219 : Bounds (8693429 / 100000000) (86934291 / 1000000000) (Real.log (43633 / 40000)) := by
  have h := reflection_log_4219_neg
  have he : Real.log (43633 / 40000) = -Real.log (40000 / 43633) := by
    rw [show ((43633 / 40000) : ℝ) = ((40000 / 43633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4220_neg : (23804421 / 250000000) ≤ -Real.log (36367 / 40000) ∧
    -Real.log (36367 / 40000) ≤ (19043537 / 200000000) := by
  have h := checkLog_sound (w := (3633 / 76367)) (n := 12)
    (lo := (23804421 / 250000000)) (hi := (19043537 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36367) = 1/(36367 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4220 : Bounds (-19043537 / 200000000) (-23804421 / 250000000) (Real.log (36367 / 40000)) := by
  have h := reflection_log_4220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4221_neg : (8283393 / 1000000000) ≤ -Real.log (1586801311 / 1600000000) ∧
    -Real.log (1586801311 / 1600000000) ≤ (4141697 / 500000000) := by
  have h := checkLog_sound (w := (13198689 / 3186801311)) (n := 12)
    (lo := (8283393 / 1000000000)) (hi := (4141697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1586801311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1586801311) = 1/(1586801311 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4221 : Bounds (-4141697 / 500000000) (-8283393 / 1000000000) (Real.log (1586801311 / 1600000000)) := by
  have h := reflection_log_4221_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4222_neg : (1648191 / 200000000) ≤ -Real.log (991792908351 / 1000000000000) ∧
    -Real.log (991792908351 / 1000000000000) ≤ (2060239 / 250000000) := by
  have h := checkLog_sound (w := (8207091649 / 1991792908351)) (n := 12)
    (lo := (1648191 / 200000000)) (hi := (2060239 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991792908351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991792908351) = 1/(991792908351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4222 : Bounds (-2060239 / 250000000) (-1648191 / 200000000) (Real.log (991792908351 / 1000000000000)) := by
  have h := reflection_log_4222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4223_neg : (1453473 / 8000000) ≤ -Real.log (250000000000 / 299808831469) ∧
    -Real.log (250000000000 / 299808831469) ≤ (90842063 / 500000000) := by
  have h := checkLog_sound (w := (49808831469 / 549808831469)) (n := 12)
    (lo := (1453473 / 8000000)) (hi := (90842063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299808831469 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299808831469 / 250000000000) = 1/(250000000000 / 299808831469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4223 : Bounds (1453473 / 8000000) (90842063 / 500000000) (Real.log (299808831469 / 250000000000)) := by
  have h := reflection_log_4223_neg
  have he : Real.log (299808831469 / 250000000000) = -Real.log (250000000000 / 299808831469) := by
    rw [show ((299808831469 / 250000000000) : ℝ) = ((250000000000 / 299808831469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
