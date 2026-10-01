import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12288_neg : (104856893 / 100000000) ≤ -Real.log (125000000000 / 356695568401) ∧
    -Real.log (125000000000 / 356695568401) ≤ (262142233 / 250000000) := by
  have h := checkLog_sound (w := (106695568401 / 606695568401)) (n := 12)
    (lo := (1421687 / 4000000)) (hi := (355421751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356695568401 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(356695568401 / 250000000000) = 1/(125000000000 / 356695568401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12288 : Bounds (104856893 / 100000000) (262142233 / 250000000) (Real.log (356695568401 / 125000000000)) := by
  have h := reflection_log_12288_neg
  have he : Real.log (356695568401 / 125000000000) = -Real.log (125000000000 / 356695568401) := by
    rw [show ((356695568401 / 125000000000) : ℝ) = ((125000000000 / 356695568401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12289_neg : (196696263 / 500000000) ≤ -Real.log (500 / 741) ∧
    -Real.log (500 / 741) ≤ (393392527 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 1241)) (n := 12)
    (lo := (196696263 / 500000000)) (hi := (393392527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741 / 500) = 1/(500 / 741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12289 : Bounds (196696263 / 500000000) (393392527 / 1000000000) (Real.log (741 / 500)) := by
  have h := reflection_log_12289_neg
  have he : Real.log (741 / 500) = -Real.log (500 / 741) := by
    rw [show ((741 / 500) : ℝ) = ((500 / 741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12290_neg : (164445009 / 250000000) ≤ -Real.log (259 / 500) ∧
    -Real.log (259 / 500) ≤ (657780037 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 759)) (n := 12)
    (lo := (164445009 / 250000000)) (hi := (657780037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 259) = 1/(259 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12290 : Bounds (-657780037 / 1000000000) (-164445009 / 250000000) (Real.log (259 / 500)) := by
  have h := reflection_log_12290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12291_neg : (481883 / 1000000000) ≤ -Real.log (500000 / 500241) ∧
    -Real.log (500000 / 500241) ≤ (120471 / 250000000) := by
  have h := checkLog_sound (w := (241 / 1000241)) (n := 12)
    (lo := (481883 / 1000000000)) (hi := (120471 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500241 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500241 / 500000) = 1/(500000 / 500241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12291 : Bounds (481883 / 1000000000) (120471 / 250000000) (Real.log (500241 / 500000)) := by
  have h := reflection_log_12291_neg
  have he : Real.log (500241 / 500000) = -Real.log (500000 / 500241) := by
    rw [show ((500241 / 500000) : ℝ) = ((500000 / 500241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12292_neg : (120529 / 250000000) ≤ -Real.log (499759 / 500000) ∧
    -Real.log (499759 / 500000) ≤ (482117 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 999759)) (n := 12)
    (lo := (120529 / 250000000)) (hi := (482117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499759) = 1/(499759 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12292 : Bounds (-482117 / 1000000000) (-120529 / 250000000) (Real.log (499759 / 500000)) := by
  have h := reflection_log_12292_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12293_neg : (223991991 / 1000000000) ≤ -Real.log (1000000 / 1251061) ∧
    -Real.log (1000000 / 1251061) ≤ (27998999 / 125000000) := by
  have h := checkLog_sound (w := (251061 / 2251061)) (n := 12)
    (lo := (223991991 / 1000000000)) (hi := (27998999 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251061 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251061 / 1000000) = 1/(1000000 / 1251061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12293 : Bounds (223991991 / 1000000000) (27998999 / 125000000) (Real.log (1251061 / 1000000)) := by
  have h := reflection_log_12293_neg
  have he : Real.log (1251061 / 1000000) = -Real.log (1000000 / 1251061) := by
    rw [show ((1251061 / 1000000) : ℝ) = ((1000000 / 1251061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12294_neg : (14454887 / 50000000) ≤ -Real.log (748939 / 1000000) ∧
    -Real.log (748939 / 1000000) ≤ (289097741 / 1000000000) := by
  have h := checkLog_sound (w := (251061 / 1748939)) (n := 12)
    (lo := (14454887 / 50000000)) (hi := (289097741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 748939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 748939) = 1/(748939 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12294 : Bounds (-289097741 / 1000000000) (-14454887 / 50000000) (Real.log (748939 / 1000000)) := by
  have h := reflection_log_12294_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12295_neg : (224814953 / 1000000000) ≤ -Real.log (1000000 / 1252091) ∧
    -Real.log (1000000 / 1252091) ≤ (112407477 / 500000000) := by
  have h := checkLog_sound (w := (252091 / 2252091)) (n := 12)
    (lo := (224814953 / 1000000000)) (hi := (112407477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252091 / 1000000) = 1/(1000000 / 1252091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12295 : Bounds (224814953 / 1000000000) (112407477 / 500000000) (Real.log (1252091 / 1000000)) := by
  have h := reflection_log_12295_neg
  have he : Real.log (1252091 / 1000000) = -Real.log (1000000 / 1252091) := by
    rw [show ((1252091 / 1000000) : ℝ) = ((1000000 / 1252091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12296_neg : (145236983 / 500000000) ≤ -Real.log (747909 / 1000000) ∧
    -Real.log (747909 / 1000000) ≤ (290473967 / 1000000000) := by
  have h := checkLog_sound (w := (252091 / 1747909)) (n := 12)
    (lo := (145236983 / 500000000)) (hi := (290473967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747909) = 1/(747909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12296 : Bounds (-290473967 / 1000000000) (-145236983 / 500000000) (Real.log (747909 / 1000000)) := by
  have h := reflection_log_12296_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12297_neg : (16414753 / 250000000) ≤ -Real.log (936450127719 / 1000000000000) ∧
    -Real.log (936450127719 / 1000000000000) ≤ (65659013 / 1000000000) := by
  have h := checkLog_sound (w := (63549872281 / 1936450127719)) (n := 12)
    (lo := (16414753 / 250000000)) (hi := (65659013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 936450127719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 936450127719) = 1/(936450127719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12297 : Bounds (-65659013 / 1000000000) (-16414753 / 250000000) (Real.log (936450127719 / 1000000000000)) := by
  have h := reflection_log_12297_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12298_neg : (65105749 / 1000000000) ≤ -Real.log (936968374279 / 1000000000000) ∧
    -Real.log (936968374279 / 1000000000000) ≤ (260423 / 4000000) := by
  have h := checkLog_sound (w := (63031625721 / 1936968374279)) (n := 12)
    (lo := (65105749 / 1000000000)) (hi := (260423 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 936968374279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 936968374279) = 1/(936968374279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12298 : Bounds (-260423 / 4000000) (-65105749 / 1000000000) (Real.log (936968374279 / 1000000000000)) := by
  have h := reflection_log_12298_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12299_neg : (513089731 / 1000000000) ≤ -Real.log (500000000000 / 835222227711) ∧
    -Real.log (500000000000 / 835222227711) ≤ (128272433 / 250000000) := by
  have h := checkLog_sound (w := (335222227711 / 1335222227711)) (n := 12)
    (lo := (513089731 / 1000000000)) (hi := (128272433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((835222227711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(835222227711 / 500000000000) = 1/(500000000000 / 835222227711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12299 : Bounds (513089731 / 1000000000) (128272433 / 250000000) (Real.log (835222227711 / 500000000000)) := by
  have h := reflection_log_12299_neg
  have he : Real.log (835222227711 / 500000000000) = -Real.log (500000000000 / 835222227711) := by
    rw [show ((835222227711 / 500000000000) : ℝ) = ((500000000000 / 835222227711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12300_neg : (515288919 / 1000000000) ≤ -Real.log (31250000000 / 52316316223) ∧
    -Real.log (31250000000 / 52316316223) ≤ (12882223 / 25000000) := by
  have h := checkLog_sound (w := (21066316223 / 83566316223)) (n := 12)
    (lo := (515288919 / 1000000000)) (hi := (12882223 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52316316223 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(52316316223 / 31250000000) = 1/(31250000000 / 52316316223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12300 : Bounds (515288919 / 1000000000) (12882223 / 25000000) (Real.log (52316316223 / 31250000000)) := by
  have h := reflection_log_12300_neg
  have he : Real.log (52316316223 / 31250000000) = -Real.log (31250000000 / 52316316223) := by
    rw [show ((52316316223 / 31250000000) : ℝ) = ((31250000000 / 52316316223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12301_neg : (104856893 / 100000000) ≤ -Real.log (500000000000 / 1426782273603) ∧
    -Real.log (500000000000 / 1426782273603) ≤ (262142233 / 250000000) := by
  have h := checkLog_sound (w := (426782273603 / 2426782273603)) (n := 12)
    (lo := (1421687 / 4000000)) (hi := (355421751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1426782273603 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1426782273603 / 1000000000000) = 1/(500000000000 / 1426782273603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12301 : Bounds (104856893 / 100000000) (262142233 / 250000000) (Real.log (1426782273603 / 500000000000)) := by
  have h := reflection_log_12301_neg
  have he : Real.log (1426782273603 / 500000000000) = -Real.log (500000000000 / 1426782273603) := by
    rw [show ((1426782273603 / 500000000000) : ℝ) = ((500000000000 / 1426782273603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12302_neg : (1051172563 / 1000000000) ≤ -Real.log (250000000000 / 715250965251) ∧
    -Real.log (250000000000 / 715250965251) ≤ (210234513 / 200000000) := by
  have h := checkLog_sound (w := (215250965251 / 1215250965251)) (n := 12)
    (lo := (358025383 / 1000000000)) (hi := (44753173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715250965251 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(715250965251 / 500000000000) = 1/(250000000000 / 715250965251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12302 : Bounds (1051172563 / 1000000000) (210234513 / 200000000) (Real.log (715250965251 / 250000000000)) := by
  have h := reflection_log_12302_neg
  have he : Real.log (715250965251 / 250000000000) = -Real.log (250000000000 / 715250965251) := by
    rw [show ((715250965251 / 250000000000) : ℝ) = ((250000000000 / 715250965251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12303_neg : (394067063 / 1000000000) ≤ -Real.log (1000 / 1483) ∧
    -Real.log (1000 / 1483) ≤ (49258383 / 125000000) := by
  have h := checkLog_sound (w := (483 / 2483)) (n := 12)
    (lo := (394067063 / 1000000000)) (hi := (49258383 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1483 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1483 / 1000) = 1/(1000 / 1483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12303 : Bounds (394067063 / 1000000000) (49258383 / 125000000) (Real.log (1483 / 1000)) := by
  have h := reflection_log_12303_neg
  have he : Real.log (1483 / 1000) = -Real.log (1000 / 1483) := by
    rw [show ((1483 / 1000) : ℝ) = ((1000 / 1483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12304_neg : (164928101 / 250000000) ≤ -Real.log (517 / 1000) ∧
    -Real.log (517 / 1000) ≤ (131942481 / 200000000) := by
  have h := checkLog_sound (w := (483 / 1517)) (n := 12)
    (lo := (164928101 / 250000000)) (hi := (131942481 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 517) = 1/(517 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12304 : Bounds (-131942481 / 200000000) (-164928101 / 250000000) (Real.log (517 / 1000)) := by
  have h := reflection_log_12304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12305_neg : (482883 / 1000000000) ≤ -Real.log (1000000 / 1000483) ∧
    -Real.log (1000000 / 1000483) ≤ (120721 / 250000000) := by
  have h := checkLog_sound (w := (483 / 2000483)) (n := 12)
    (lo := (482883 / 1000000000)) (hi := (120721 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000483 / 1000000) = 1/(1000000 / 1000483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12305 : Bounds (482883 / 1000000000) (120721 / 250000000) (Real.log (1000483 / 1000000)) := by
  have h := reflection_log_12305_neg
  have he : Real.log (1000483 / 1000000) = -Real.log (1000000 / 1000483) := by
    rw [show ((1000483 / 1000000) : ℝ) = ((1000000 / 1000483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12306_neg : (120779 / 250000000) ≤ -Real.log (999517 / 1000000) ∧
    -Real.log (999517 / 1000000) ≤ (483117 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 1999517)) (n := 12)
    (lo := (120779 / 250000000)) (hi := (483117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999517) = 1/(999517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12306 : Bounds (-483117 / 1000000000) (-120779 / 250000000) (Real.log (999517 / 1000000)) := by
  have h := reflection_log_12306_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12307_neg : (89779 / 400000) ≤ -Real.log (1000000 / 1251631) ∧
    -Real.log (1000000 / 1251631) ≤ (224447501 / 1000000000) := by
  have h := checkLog_sound (w := (251631 / 2251631)) (n := 12)
    (lo := (89779 / 400000)) (hi := (224447501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251631 / 1000000) = 1/(1000000 / 1251631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12307 : Bounds (89779 / 400000) (224447501 / 1000000000) (Real.log (1251631 / 1000000)) := by
  have h := reflection_log_12307_neg
  have he : Real.log (1251631 / 1000000) = -Real.log (1000000 / 1251631) := by
    rw [show ((1251631 / 1000000) : ℝ) = ((1000000 / 1251631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12308_neg : (289859107 / 1000000000) ≤ -Real.log (748369 / 1000000) ∧
    -Real.log (748369 / 1000000) ≤ (72464777 / 250000000) := by
  have h := checkLog_sound (w := (251631 / 1748369)) (n := 12)
    (lo := (289859107 / 1000000000)) (hi := (72464777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 748369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 748369) = 1/(748369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12308 : Bounds (-72464777 / 250000000) (-289859107 / 1000000000) (Real.log (748369 / 1000000)) := by
  have h := reflection_log_12308_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12309_neg : (45054337 / 200000000) ≤ -Real.log (1000000 / 1252663) ∧
    -Real.log (1000000 / 1252663) ≤ (112635843 / 500000000) := by
  have h := checkLog_sound (w := (252663 / 2252663)) (n := 12)
    (lo := (45054337 / 200000000)) (hi := (112635843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252663 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252663 / 1000000) = 1/(1000000 / 1252663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12309 : Bounds (45054337 / 200000000) (112635843 / 500000000) (Real.log (1252663 / 1000000)) := by
  have h := reflection_log_12309_neg
  have he : Real.log (1252663 / 1000000) = -Real.log (1000000 / 1252663) := by
    rw [show ((1252663 / 1000000) : ℝ) = ((1000000 / 1252663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12310_neg : (291239057 / 1000000000) ≤ -Real.log (747337 / 1000000) ∧
    -Real.log (747337 / 1000000) ≤ (145619529 / 500000000) := by
  have h := checkLog_sound (w := (252663 / 1747337)) (n := 12)
    (lo := (291239057 / 1000000000)) (hi := (145619529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747337) = 1/(747337 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12310 : Bounds (-145619529 / 500000000) (-291239057 / 1000000000) (Real.log (747337 / 1000000)) := by
  have h := reflection_log_12310_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12311_neg : (16491843 / 250000000) ≤ -Real.log (936161408431 / 1000000000000) ∧
    -Real.log (936161408431 / 1000000000000) ≤ (65967373 / 1000000000) := by
  have h := checkLog_sound (w := (63838591569 / 1936161408431)) (n := 12)
    (lo := (16491843 / 250000000)) (hi := (65967373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 936161408431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 936161408431) = 1/(936161408431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12311 : Bounds (-65967373 / 1000000000) (-16491843 / 250000000) (Real.log (936161408431 / 1000000000000)) := by
  have h := reflection_log_12311_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12312_neg : (32705803 / 500000000) ≤ -Real.log (936681839839 / 1000000000000) ∧
    -Real.log (936681839839 / 1000000000000) ≤ (65411607 / 1000000000) := by
  have h := checkLog_sound (w := (63318160161 / 1936681839839)) (n := 12)
    (lo := (32705803 / 500000000)) (hi := (65411607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 936681839839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 936681839839) = 1/(936681839839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12312 : Bounds (-65411607 / 1000000000) (-32705803 / 500000000) (Real.log (936681839839 / 1000000000000)) := by
  have h := reflection_log_12312_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12313_neg : (514306607 / 1000000000) ≤ -Real.log (250000000000 / 418119604099) ∧
    -Real.log (250000000000 / 418119604099) ≤ (32144163 / 62500000) := by
  have h := checkLog_sound (w := (168119604099 / 668119604099)) (n := 12)
    (lo := (514306607 / 1000000000)) (hi := (32144163 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((418119604099 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(418119604099 / 250000000000) = 1/(250000000000 / 418119604099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12313 : Bounds (514306607 / 1000000000) (32144163 / 62500000) (Real.log (418119604099 / 250000000000)) := by
  have h := reflection_log_12313_neg
  have he : Real.log (418119604099 / 250000000000) = -Real.log (250000000000 / 418119604099) := by
    rw [show ((418119604099 / 250000000000) : ℝ) = ((250000000000 / 418119604099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12314_neg : (258255371 / 500000000) ≤ -Real.log (500000000000 / 838084425099) ∧
    -Real.log (500000000000 / 838084425099) ≤ (516510743 / 1000000000) := by
  have h := checkLog_sound (w := (338084425099 / 1338084425099)) (n := 12)
    (lo := (258255371 / 500000000)) (hi := (516510743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((838084425099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(838084425099 / 500000000000) = 1/(500000000000 / 838084425099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12314 : Bounds (258255371 / 500000000) (516510743 / 1000000000) (Real.log (838084425099 / 500000000000)) := by
  have h := reflection_log_12314_neg
  have he : Real.log (838084425099 / 500000000000) = -Real.log (500000000000 / 838084425099) := by
    rw [show ((838084425099 / 500000000000) : ℝ) = ((500000000000 / 838084425099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12315_neg : (1051172563 / 1000000000) ≤ -Real.log (500000000000 / 1430501930501) ∧
    -Real.log (500000000000 / 1430501930501) ≤ (210234513 / 200000000) := by
  have h := checkLog_sound (w := (430501930501 / 2430501930501)) (n := 12)
    (lo := (358025383 / 1000000000)) (hi := (44753173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1430501930501 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1430501930501 / 1000000000000) = 1/(500000000000 / 1430501930501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12315 : Bounds (1051172563 / 1000000000) (210234513 / 200000000) (Real.log (1430501930501 / 500000000000)) := by
  have h := reflection_log_12315_neg
  have he : Real.log (1430501930501 / 500000000000) = -Real.log (500000000000 / 1430501930501) := by
    rw [show ((1430501930501 / 500000000000) : ℝ) = ((500000000000 / 1430501930501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12316_neg : (1053779467 / 1000000000) ≤ -Real.log (50000000000 / 143423597679) ∧
    -Real.log (50000000000 / 143423597679) ≤ (1053779469 / 1000000000) := by
  have h := checkLog_sound (w := (43423597679 / 243423597679)) (n := 12)
    (lo := (360632287 / 1000000000)) (hi := (11269759 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143423597679 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(143423597679 / 100000000000) = 1/(50000000000 / 143423597679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12316 : Bounds (1053779467 / 1000000000) (1053779469 / 1000000000) (Real.log (143423597679 / 50000000000)) := by
  have h := reflection_log_12316_neg
  have he : Real.log (143423597679 / 50000000000) = -Real.log (50000000000 / 143423597679) := by
    rw [show ((143423597679 / 50000000000) : ℝ) = ((50000000000 / 143423597679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12317_neg : (49342643 / 125000000) ≤ -Real.log (250 / 371) ∧
    -Real.log (250 / 371) ≤ (78948229 / 200000000) := by
  have h := checkLog_sound (w := (121 / 621)) (n := 12)
    (lo := (49342643 / 125000000)) (hi := (78948229 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((371 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(371 / 250) = 1/(250 / 371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12317 : Bounds (49342643 / 125000000) (78948229 / 200000000) (Real.log (371 / 250)) := by
  have h := reflection_log_12317_neg
  have he : Real.log (371 / 250) = -Real.log (250 / 371) := by
    rw [show ((371 / 250) : ℝ) = ((250 / 371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12318_neg : (661648513 / 1000000000) ≤ -Real.log (129 / 250) ∧
    -Real.log (129 / 250) ≤ (330824257 / 500000000) := by
  have h := checkLog_sound (w := (121 / 379)) (n := 12)
    (lo := (661648513 / 1000000000)) (hi := (330824257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 129) = 1/(129 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12318 : Bounds (-330824257 / 500000000) (-661648513 / 1000000000) (Real.log (129 / 250)) := by
  have h := reflection_log_12318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12319_neg : (241941 / 500000000) ≤ -Real.log (250000 / 250121) ∧
    -Real.log (250000 / 250121) ≤ (483883 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 500121)) (n := 12)
    (lo := (241941 / 500000000)) (hi := (483883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250121 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250121 / 250000) = 1/(250000 / 250121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12319 : Bounds (241941 / 500000000) (483883 / 1000000000) (Real.log (250121 / 250000)) := by
  have h := reflection_log_12319_neg
  have he : Real.log (250121 / 250000) = -Real.log (250000 / 250121) := by
    rw [show ((250121 / 250000) : ℝ) = ((250000 / 250121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12320_neg : (484117 / 1000000000) ≤ -Real.log (249879 / 250000) ∧
    -Real.log (249879 / 250000) ≤ (242059 / 500000000) := by
  have h := checkLog_sound (w := (121 / 499879)) (n := 12)
    (lo := (484117 / 1000000000)) (hi := (242059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249879) = 1/(249879 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12320 : Bounds (-242059 / 500000000) (-484117 / 1000000000) (Real.log (249879 / 250000)) := by
  have h := reflection_log_12320_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12321_neg : (224903601 / 1000000000) ≤ -Real.log (500000 / 626101) ∧
    -Real.log (500000 / 626101) ≤ (112451801 / 500000000) := by
  have h := checkLog_sound (w := (126101 / 1126101)) (n := 12)
    (lo := (224903601 / 1000000000)) (hi := (112451801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626101 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626101 / 500000) = 1/(500000 / 626101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12321 : Bounds (224903601 / 1000000000) (112451801 / 500000000) (Real.log (626101 / 500000)) := by
  have h := reflection_log_12321_neg
  have he : Real.log (626101 / 500000) = -Real.log (500000 / 626101) := by
    rw [show ((626101 / 500000) : ℝ) = ((500000 / 626101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12322_neg : (29062239 / 100000000) ≤ -Real.log (373899 / 500000) ∧
    -Real.log (373899 / 500000) ≤ (290622391 / 1000000000) := by
  have h := checkLog_sound (w := (126101 / 873899)) (n := 12)
    (lo := (29062239 / 100000000)) (hi := (290622391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 373899) = 1/(373899 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12322 : Bounds (-290622391 / 1000000000) (-29062239 / 100000000) (Real.log (373899 / 500000)) := by
  have h := reflection_log_12322_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12323_neg : (14108013 / 62500000) ≤ -Real.log (200000 / 250647) ∧
    -Real.log (200000 / 250647) ≤ (225728209 / 1000000000) := by
  have h := checkLog_sound (w := (50647 / 450647)) (n := 12)
    (lo := (14108013 / 62500000)) (hi := (225728209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250647 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250647 / 200000) = 1/(200000 / 250647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12323 : Bounds (14108013 / 62500000) (225728209 / 1000000000) (Real.log (250647 / 200000)) := by
  have h := reflection_log_12323_neg
  have he : Real.log (250647 / 200000) = -Real.log (200000 / 250647) := by
    rw [show ((250647 / 200000) : ℝ) = ((200000 / 250647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12324_neg : (58400947 / 200000000) ≤ -Real.log (149353 / 200000) ∧
    -Real.log (149353 / 200000) ≤ (2281287 / 7812500) := by
  have h := checkLog_sound (w := (50647 / 349353)) (n := 12)
    (lo := (58400947 / 200000000)) (hi := (2281287 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 149353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 149353) = 1/(149353 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12324 : Bounds (-2281287 / 7812500) (-58400947 / 200000000) (Real.log (149353 / 200000)) := by
  have h := reflection_log_12324_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12325_neg : (33138263 / 500000000) ≤ -Real.log (37434881391 / 40000000000) ∧
    -Real.log (37434881391 / 40000000000) ≤ (66276527 / 1000000000) := by
  have h := checkLog_sound (w := (2565118609 / 77434881391)) (n := 12)
    (lo := (33138263 / 500000000)) (hi := (66276527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37434881391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37434881391) = 1/(37434881391 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12325 : Bounds (-66276527 / 1000000000) (-33138263 / 500000000) (Real.log (37434881391 / 40000000000)) := by
  have h := reflection_log_12325_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12326_neg : (65718789 / 1000000000) ≤ -Real.log (234098537799 / 250000000000) ∧
    -Real.log (234098537799 / 250000000000) ≤ (6571879 / 100000000) := by
  have h := checkLog_sound (w := (15901462201 / 484098537799)) (n := 12)
    (lo := (65718789 / 1000000000)) (hi := (6571879 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 234098537799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 234098537799) = 1/(234098537799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12326 : Bounds (-6571879 / 100000000) (-65718789 / 1000000000) (Real.log (234098537799 / 250000000000)) := by
  have h := reflection_log_12326_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12327_neg : (64440749 / 125000000) ≤ -Real.log (100000000000 / 167451905461) ∧
    -Real.log (100000000000 / 167451905461) ≤ (515525993 / 1000000000) := by
  have h := checkLog_sound (w := (67451905461 / 267451905461)) (n := 12)
    (lo := (64440749 / 125000000)) (hi := (515525993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167451905461 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167451905461 / 100000000000) = 1/(100000000000 / 167451905461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12327 : Bounds (64440749 / 125000000) (515525993 / 1000000000) (Real.log (167451905461 / 100000000000)) := by
  have h := reflection_log_12327_neg
  have he : Real.log (167451905461 / 100000000000) = -Real.log (100000000000 / 167451905461) := by
    rw [show ((167451905461 / 100000000000) : ℝ) = ((100000000000 / 167451905461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12328_neg : (517732943 / 1000000000) ≤ -Real.log (250000000000 / 419554679183) ∧
    -Real.log (250000000000 / 419554679183) ≤ (32358309 / 62500000) := by
  have h := checkLog_sound (w := (169554679183 / 669554679183)) (n := 12)
    (lo := (517732943 / 1000000000)) (hi := (32358309 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419554679183 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(419554679183 / 250000000000) = 1/(250000000000 / 419554679183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12328 : Bounds (517732943 / 1000000000) (32358309 / 62500000) (Real.log (419554679183 / 250000000000)) := by
  have h := reflection_log_12328_neg
  have he : Real.log (419554679183 / 250000000000) = -Real.log (250000000000 / 419554679183) := by
    rw [show ((419554679183 / 250000000000) : ℝ) = ((250000000000 / 419554679183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12329_neg : (1053779467 / 1000000000) ≤ -Real.log (500000000000 / 1434235976789) ∧
    -Real.log (500000000000 / 1434235976789) ≤ (1053779469 / 1000000000) := by
  have h := checkLog_sound (w := (434235976789 / 2434235976789)) (n := 12)
    (lo := (360632287 / 1000000000)) (hi := (11269759 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1434235976789 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1434235976789 / 1000000000000) = 1/(500000000000 / 1434235976789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12329 : Bounds (1053779467 / 1000000000) (1053779469 / 1000000000) (Real.log (1434235976789 / 500000000000)) := by
  have h := reflection_log_12329_neg
  have he : Real.log (1434235976789 / 500000000000) = -Real.log (500000000000 / 1434235976789) := by
    rw [show ((1434235976789 / 500000000000) : ℝ) = ((500000000000 / 1434235976789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12330_neg : (1056389657 / 1000000000) ≤ -Real.log (4000000000 / 11503875969) ∧
    -Real.log (4000000000 / 11503875969) ≤ (1056389659 / 1000000000) := by
  have h := checkLog_sound (w := (3503875969 / 19503875969)) (n := 12)
    (lo := (363242477 / 1000000000)) (hi := (181621239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11503875969 / 8000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(11503875969 / 8000000000) = 1/(4000000000 / 11503875969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12330 : Bounds (1056389657 / 1000000000) (1056389659 / 1000000000) (Real.log (11503875969 / 4000000000)) := by
  have h := reflection_log_12330_neg
  have he : Real.log (11503875969 / 4000000000) = -Real.log (4000000000 / 11503875969) := by
    rw [show ((11503875969 / 4000000000) : ℝ) = ((4000000000 / 11503875969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12331_neg : (98853693 / 250000000) ≤ -Real.log (200 / 297) ∧
    -Real.log (200 / 297) ≤ (395414773 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 497)) (n := 12)
    (lo := (98853693 / 250000000)) (hi := (395414773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297 / 200) = 1/(200 / 297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12331 : Bounds (98853693 / 250000000) (395414773 / 1000000000) (Real.log (297 / 200)) := by
  have h := reflection_log_12331_neg
  have he : Real.log (297 / 200) = -Real.log (200 / 297) := by
    rw [show ((297 / 200) : ℝ) = ((200 / 297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12332_neg : (331794189 / 500000000) ≤ -Real.log (103 / 200) ∧
    -Real.log (103 / 200) ≤ (663588379 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 303)) (n := 12)
    (lo := (331794189 / 500000000)) (hi := (663588379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 103) = 1/(103 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12332 : Bounds (-663588379 / 1000000000) (-331794189 / 500000000) (Real.log (103 / 200)) := by
  have h := reflection_log_12332_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12333_neg : (242441 / 500000000) ≤ -Real.log (200000 / 200097) ∧
    -Real.log (200000 / 200097) ≤ (484883 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 400097)) (n := 12)
    (lo := (242441 / 500000000)) (hi := (484883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200097 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200097 / 200000) = 1/(200000 / 200097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12333 : Bounds (242441 / 500000000) (484883 / 1000000000) (Real.log (200097 / 200000)) := by
  have h := reflection_log_12333_neg
  have he : Real.log (200097 / 200000) = -Real.log (200000 / 200097) := by
    rw [show ((200097 / 200000) : ℝ) = ((200000 / 200097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12334_neg : (485117 / 1000000000) ≤ -Real.log (199903 / 200000) ∧
    -Real.log (199903 / 200000) ≤ (242559 / 500000000) := by
  have h := checkLog_sound (w := (97 / 399903)) (n := 12)
    (lo := (485117 / 1000000000)) (hi := (242559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199903) = 1/(199903 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12334 : Bounds (-242559 / 500000000) (-485117 / 1000000000) (Real.log (199903 / 200000)) := by
  have h := reflection_log_12334_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12335_neg : (112679747 / 500000000) ≤ -Real.log (1000000 / 1252773) ∧
    -Real.log (1000000 / 1252773) ≤ (45071899 / 200000000) := by
  have h := checkLog_sound (w := (252773 / 2252773)) (n := 12)
    (lo := (112679747 / 500000000)) (hi := (45071899 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252773 / 1000000) = 1/(1000000 / 1252773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12335 : Bounds (112679747 / 500000000) (45071899 / 200000000) (Real.log (1252773 / 1000000)) := by
  have h := reflection_log_12335_neg
  have he : Real.log (1252773 / 1000000) = -Real.log (1000000 / 1252773) := by
    rw [show ((1252773 / 1000000) : ℝ) = ((1000000 / 1252773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12336_neg : (291386257 / 1000000000) ≤ -Real.log (747227 / 1000000) ∧
    -Real.log (747227 / 1000000) ≤ (145693129 / 500000000) := by
  have h := checkLog_sound (w := (252773 / 1747227)) (n := 12)
    (lo := (291386257 / 1000000000)) (hi := (145693129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747227) = 1/(747227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12336 : Bounds (-145693129 / 500000000) (-291386257 / 1000000000) (Real.log (747227 / 1000000)) := by
  have h := reflection_log_12336_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12337_neg : (113092261 / 500000000) ≤ -Real.log (1000000 / 1253807) ∧
    -Real.log (1000000 / 1253807) ≤ (226184523 / 1000000000) := by
  have h := checkLog_sound (w := (253807 / 2253807)) (n := 12)
    (lo := (113092261 / 500000000)) (hi := (226184523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253807 / 1000000) = 1/(1000000 / 1253807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12337 : Bounds (113092261 / 500000000) (226184523 / 1000000000) (Real.log (1253807 / 1000000)) := by
  have h := reflection_log_12337_neg
  have he : Real.log (1253807 / 1000000) = -Real.log (1000000 / 1253807) := by
    rw [show ((1253807 / 1000000) : ℝ) = ((1000000 / 1253807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12338_neg : (292770999 / 1000000000) ≤ -Real.log (746193 / 1000000) ∧
    -Real.log (746193 / 1000000) ≤ (292771 / 1000000) := by
  have h := checkLog_sound (w := (253807 / 1746193)) (n := 12)
    (lo := (292770999 / 1000000000)) (hi := (292771 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 746193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 746193) = 1/(746193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12338 : Bounds (-292771 / 1000000) (-292770999 / 1000000000) (Real.log (746193 / 1000000)) := by
  have h := reflection_log_12338_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12339_neg : (16646619 / 250000000) ≤ -Real.log (935582006751 / 1000000000000) ∧
    -Real.log (935582006751 / 1000000000000) ≤ (66586477 / 1000000000) := by
  have h := checkLog_sound (w := (64417993249 / 1935582006751)) (n := 12)
    (lo := (16646619 / 250000000)) (hi := (66586477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 935582006751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 935582006751) = 1/(935582006751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12339 : Bounds (-66586477 / 1000000000) (-16646619 / 250000000) (Real.log (935582006751 / 1000000000000)) := by
  have h := reflection_log_12339_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12340_neg : (66026763 / 1000000000) ≤ -Real.log (936105810471 / 1000000000000) ∧
    -Real.log (936105810471 / 1000000000000) ≤ (16506691 / 250000000) := by
  have h := checkLog_sound (w := (63894189529 / 1936105810471)) (n := 12)
    (lo := (66026763 / 1000000000)) (hi := (16506691 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 936105810471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 936105810471) = 1/(936105810471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12340 : Bounds (-16506691 / 250000000) (-66026763 / 1000000000) (Real.log (936105810471 / 1000000000000)) := by
  have h := reflection_log_12340_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12341_neg : (64593219 / 125000000) ≤ -Real.log (62500000000 / 104785175723) ∧
    -Real.log (62500000000 / 104785175723) ≤ (516745753 / 1000000000) := by
  have h := checkLog_sound (w := (42285175723 / 167285175723)) (n := 12)
    (lo := (64593219 / 125000000)) (hi := (516745753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104785175723 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(104785175723 / 62500000000) = 1/(62500000000 / 104785175723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12341 : Bounds (64593219 / 125000000) (516745753 / 1000000000) (Real.log (104785175723 / 62500000000)) := by
  have h := reflection_log_12341_neg
  have he : Real.log (104785175723 / 62500000000) = -Real.log (62500000000 / 104785175723) := by
    rw [show ((104785175723 / 62500000000) : ℝ) = ((62500000000 / 104785175723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12342_neg : (518955521 / 1000000000) ≤ -Real.log (250000000000 / 420067931487) ∧
    -Real.log (250000000000 / 420067931487) ≤ (259477761 / 500000000) := by
  have h := checkLog_sound (w := (170067931487 / 670067931487)) (n := 12)
    (lo := (518955521 / 1000000000)) (hi := (259477761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((420067931487 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(420067931487 / 250000000000) = 1/(250000000000 / 420067931487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12342 : Bounds (518955521 / 1000000000) (259477761 / 500000000) (Real.log (420067931487 / 250000000000)) := by
  have h := reflection_log_12342_neg
  have he : Real.log (420067931487 / 250000000000) = -Real.log (250000000000 / 420067931487) := by
    rw [show ((420067931487 / 250000000000) : ℝ) = ((250000000000 / 420067931487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12343_neg : (1056389657 / 1000000000) ≤ -Real.log (125000000000 / 359496124031) ∧
    -Real.log (125000000000 / 359496124031) ≤ (1056389659 / 1000000000) := by
  have h := checkLog_sound (w := (109496124031 / 609496124031)) (n := 12)
    (lo := (363242477 / 1000000000)) (hi := (181621239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359496124031 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(359496124031 / 250000000000) = 1/(125000000000 / 359496124031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12343 : Bounds (1056389657 / 1000000000) (1056389659 / 1000000000) (Real.log (359496124031 / 125000000000)) := by
  have h := reflection_log_12343_neg
  have he : Real.log (359496124031 / 125000000000) = -Real.log (125000000000 / 359496124031) := by
    rw [show ((359496124031 / 125000000000) : ℝ) = ((125000000000 / 359496124031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12344_neg : (21180063 / 20000000) ≤ -Real.log (31250000000 / 90109223301) ∧
    -Real.log (31250000000 / 90109223301) ≤ (66187697 / 62500000) := by
  have h := checkLog_sound (w := (27609223301 / 152609223301)) (n := 12)
    (lo := (36585597 / 100000000)) (hi := (365855971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90109223301 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(90109223301 / 62500000000) = 1/(31250000000 / 90109223301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12344 : Bounds (21180063 / 20000000) (66187697 / 62500000) (Real.log (90109223301 / 31250000000)) := by
  have h := reflection_log_12344_neg
  have he : Real.log (90109223301 / 31250000000) = -Real.log (31250000000 / 90109223301) := by
    rw [show ((90109223301 / 31250000000) : ℝ) = ((31250000000 / 90109223301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12345_neg : (198043973 / 500000000) ≤ -Real.log (500 / 743) ∧
    -Real.log (500 / 743) ≤ (396087947 / 1000000000) := by
  have h := checkLog_sound (w := (243 / 1243)) (n := 12)
    (lo := (198043973 / 500000000)) (hi := (396087947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743 / 500) = 1/(500 / 743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12345 : Bounds (198043973 / 500000000) (396087947 / 1000000000) (Real.log (743 / 500)) := by
  have h := reflection_log_12345_neg
  have he : Real.log (743 / 500) = -Real.log (500 / 743) := by
    rw [show ((743 / 500) : ℝ) = ((500 / 743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12346_neg : (665532013 / 1000000000) ≤ -Real.log (257 / 500) ∧
    -Real.log (257 / 500) ≤ (332766007 / 500000000) := by
  have h := checkLog_sound (w := (243 / 757)) (n := 12)
    (lo := (665532013 / 1000000000)) (hi := (332766007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 257) = 1/(257 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12346 : Bounds (-332766007 / 500000000) (-665532013 / 1000000000) (Real.log (257 / 500)) := by
  have h := reflection_log_12346_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12347_neg : (485881 / 1000000000) ≤ -Real.log (500000 / 500243) ∧
    -Real.log (500000 / 500243) ≤ (242941 / 500000000) := by
  have h := checkLog_sound (w := (243 / 1000243)) (n := 12)
    (lo := (485881 / 1000000000)) (hi := (242941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500243 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500243 / 500000) = 1/(500000 / 500243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12347 : Bounds (485881 / 1000000000) (242941 / 500000000) (Real.log (500243 / 500000)) := by
  have h := reflection_log_12347_neg
  have he : Real.log (500243 / 500000) = -Real.log (500000 / 500243) := by
    rw [show ((500243 / 500000) : ℝ) = ((500000 / 500243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12348_neg : (243059 / 500000000) ≤ -Real.log (499757 / 500000) ∧
    -Real.log (499757 / 500000) ≤ (486119 / 1000000000) := by
  have h := checkLog_sound (w := (243 / 999757)) (n := 12)
    (lo := (243059 / 500000000)) (hi := (486119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499757) = 1/(499757 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12348 : Bounds (-486119 / 1000000000) (-243059 / 500000000) (Real.log (499757 / 500000)) := by
  have h := reflection_log_12348_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12349_neg : (225815977 / 1000000000) ≤ -Real.log (200000 / 250669) ∧
    -Real.log (200000 / 250669) ≤ (112907989 / 500000000) := by
  have h := checkLog_sound (w := (50669 / 450669)) (n := 12)
    (lo := (225815977 / 1000000000)) (hi := (112907989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250669 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250669 / 200000) = 1/(200000 / 250669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12349 : Bounds (225815977 / 1000000000) (112907989 / 500000000) (Real.log (250669 / 200000)) := by
  have h := reflection_log_12349_neg
  have he : Real.log (250669 / 200000) = -Real.log (200000 / 250669) := by
    rw [show ((250669 / 200000) : ℝ) = ((200000 / 250669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12350_neg : (292152047 / 1000000000) ≤ -Real.log (149331 / 200000) ∧
    -Real.log (149331 / 200000) ≤ (18259503 / 62500000) := by
  have h := checkLog_sound (w := (50669 / 349331)) (n := 12)
    (lo := (292152047 / 1000000000)) (hi := (18259503 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 149331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 149331) = 1/(149331 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12350 : Bounds (-18259503 / 62500000) (-292152047 / 1000000000) (Real.log (149331 / 200000)) := by
  have h := reflection_log_12350_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12351_neg : (113320713 / 500000000) ≤ -Real.log (50000 / 62719) ∧
    -Real.log (50000 / 62719) ≤ (226641427 / 1000000000) := by
  have h := checkLog_sound (w := (12719 / 112719)) (n := 12)
    (lo := (113320713 / 500000000)) (hi := (226641427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62719 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62719 / 50000) = 1/(50000 / 62719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12351 : Bounds (113320713 / 500000000) (226641427 / 1000000000) (Real.log (62719 / 50000)) := by
  have h := reflection_log_12351_neg
  have he : Real.log (62719 / 50000) = -Real.log (50000 / 62719) := by
    rw [show ((62719 / 50000) : ℝ) = ((50000 / 62719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
