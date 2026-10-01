import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13120_neg : (120245039 / 1000000000) ≤ -Real.log (55418945799 / 62500000000) ∧
    -Real.log (55418945799 / 62500000000) ≤ (1503063 / 12500000) := by
  have h := checkLog_sound (w := (7081054201 / 117918945799)) (n := 12)
    (lo := (120245039 / 1000000000)) (hi := (1503063 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 55418945799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 55418945799) = 1/(55418945799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13120 : Bounds (-1503063 / 12500000) (-120245039 / 1000000000) (Real.log (55418945799 / 62500000000)) := by
  have h := reflection_log_13120_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13121_neg : (59193347 / 500000000) ≤ -Real.log (888352465231 / 1000000000000) ∧
    -Real.log (888352465231 / 1000000000000) ≤ (23677339 / 200000000) := by
  have h := checkLog_sound (w := (111647534769 / 1888352465231)) (n := 12)
    (lo := (59193347 / 500000000)) (hi := (23677339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 888352465231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 888352465231) = 1/(888352465231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13121 : Bounds (-23677339 / 200000000) (-59193347 / 500000000) (Real.log (888352465231 / 1000000000000)) := by
  have h := reflection_log_13121_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13122_neg : (27798239 / 40000000) ≤ -Real.log (125000000000 / 250452608119) ∧
    -Real.log (125000000000 / 250452608119) ≤ (694955977 / 1000000000) := by
  have h := checkLog_sound (w := (452608119 / 500452608119)) (n := 12)
    (lo := (361759 / 200000000)) (hi := (452199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250452608119 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250452608119 / 250000000000) = 1/(125000000000 / 250452608119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13122 : Bounds (27798239 / 40000000) (694955977 / 1000000000) (Real.log (250452608119 / 125000000000)) := by
  have h := reflection_log_13122_neg
  have he : Real.log (250452608119 / 125000000000) = -Real.log (125000000000 / 250452608119) := by
    rw [show ((250452608119 / 125000000000) : ℝ) = ((125000000000 / 250452608119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13123_neg : (140099441 / 200000000) ≤ -Real.log (100000000000 / 201475420709) ∧
    -Real.log (100000000000 / 201475420709) ≤ (700497207 / 1000000000) := by
  have h := checkLog_sound (w := (1475420709 / 401475420709)) (n := 12)
    (lo := (294001 / 40000000)) (hi := (3675013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201475420709 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(201475420709 / 200000000000) = 1/(100000000000 / 201475420709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13123 : Bounds (140099441 / 200000000) (700497207 / 1000000000) (Real.log (201475420709 / 100000000000)) := by
  have h := reflection_log_13123_neg
  have he : Real.log (201475420709 / 100000000000) = -Real.log (100000000000 / 201475420709) := by
    rw [show ((201475420709 / 100000000000) : ℝ) = ((100000000000 / 201475420709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13124_neg : (725005087 / 500000000) ≤ -Real.log (62500000000 / 266447368421) ∧
    -Real.log (62500000000 / 266447368421) ≤ (1450010177 / 1000000000) := by
  have h := checkLog_sound (w := (16447368421 / 516447368421)) (n := 12)
    (lo := (31857907 / 500000000)) (hi := (12743163 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((266447368421 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(266447368421 / 250000000000) = 1/(62500000000 / 266447368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13124 : Bounds (725005087 / 500000000) (1450010177 / 1000000000) (Real.log (266447368421 / 62500000000)) := by
  have h := reflection_log_13124_neg
  have he : Real.log (266447368421 / 62500000000) = -Real.log (62500000000 / 266447368421) := by
    rw [show ((266447368421 / 62500000000) : ℝ) = ((62500000000 / 266447368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13125_neg : (729893189 / 500000000) ≤ -Real.log (5000000000 / 21525198939) ∧
    -Real.log (5000000000 / 21525198939) ≤ (1459786381 / 1000000000) := by
  have h := checkLog_sound (w := (1525198939 / 41525198939)) (n := 12)
    (lo := (36746009 / 500000000)) (hi := (73492019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21525198939 / 20000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(21525198939 / 20000000000) = 1/(5000000000 / 21525198939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13125 : Bounds (729893189 / 500000000) (1459786381 / 1000000000) (Real.log (21525198939 / 5000000000)) := by
  have h := reflection_log_13125_neg
  have he : Real.log (21525198939 / 5000000000) = -Real.log (5000000000 / 21525198939) := by
    rw [show ((21525198939 / 5000000000) : ℝ) = ((5000000000 / 21525198939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13126_neg : (486123011 / 1000000000) ≤ -Real.log (500 / 813) ∧
    -Real.log (500 / 813) ≤ (121530753 / 250000000) := by
  have h := checkLog_sound (w := (313 / 1313)) (n := 12)
    (lo := (486123011 / 1000000000)) (hi := (121530753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813 / 500) = 1/(500 / 813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13126 : Bounds (486123011 / 1000000000) (121530753 / 250000000) (Real.log (813 / 500)) := by
  have h := reflection_log_13126_neg
  have he : Real.log (813 / 500) = -Real.log (500 / 813) := by
    rw [show ((813 / 500) : ℝ) = ((500 / 813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13127_neg : (983499481 / 1000000000) ≤ -Real.log (187 / 500) ∧
    -Real.log (187 / 500) ≤ (983499483 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 437)) (n := 12)
    (lo := (290352301 / 1000000000)) (hi := (145176151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 187) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 187) = 1/(187 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13127 : Bounds (-983499483 / 1000000000) (-983499481 / 1000000000) (Real.log (187 / 500)) := by
  have h := reflection_log_13127_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13128_neg : (156451 / 250000000) ≤ -Real.log (500000 / 500313) ∧
    -Real.log (500000 / 500313) ≤ (125161 / 200000000) := by
  have h := checkLog_sound (w := (313 / 1000313)) (n := 12)
    (lo := (156451 / 250000000)) (hi := (125161 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500313 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500313 / 500000) = 1/(500000 / 500313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13128 : Bounds (156451 / 250000000) (125161 / 200000000) (Real.log (500313 / 500000)) := by
  have h := reflection_log_13128_neg
  have he : Real.log (500313 / 500000) = -Real.log (500000 / 500313) := by
    rw [show ((500313 / 500000) : ℝ) = ((500000 / 500313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13129_neg : (156549 / 250000000) ≤ -Real.log (499687 / 500000) ∧
    -Real.log (499687 / 500000) ≤ (626197 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 999687)) (n := 12)
    (lo := (156549 / 250000000)) (hi := (626197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499687) = 1/(499687 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13129 : Bounds (-626197 / 1000000000) (-156549 / 250000000) (Real.log (499687 / 500000)) := by
  have h := reflection_log_13129_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13130_neg : (72425071 / 250000000) ≤ -Real.log (1000000 / 1336027) ∧
    -Real.log (1000000 / 1336027) ≤ (57940057 / 200000000) := by
  have h := checkLog_sound (w := (336027 / 2336027)) (n := 12)
    (lo := (72425071 / 250000000)) (hi := (57940057 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1336027 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1336027 / 1000000) = 1/(1000000 / 1336027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13130 : Bounds (72425071 / 250000000) (57940057 / 200000000) (Real.log (1336027 / 1000000)) := by
  have h := reflection_log_13130_neg
  have he : Real.log (1336027 / 1000000) = -Real.log (1000000 / 1336027) := by
    rw [show ((1336027 / 1000000) : ℝ) = ((1000000 / 1336027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13131_neg : (6398653 / 15625000) ≤ -Real.log (663973 / 1000000) ∧
    -Real.log (663973 / 1000000) ≤ (409513793 / 1000000000) := by
  have h := checkLog_sound (w := (336027 / 1663973)) (n := 12)
    (lo := (6398653 / 15625000)) (hi := (409513793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 663973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 663973) = 1/(663973 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13131 : Bounds (-409513793 / 1000000000) (-6398653 / 15625000) (Real.log (663973 / 1000000)) := by
  have h := reflection_log_13131_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13132_neg : (291545101 / 1000000000) ≤ -Real.log (500000 / 669247) ∧
    -Real.log (500000 / 669247) ≤ (145772551 / 500000000) := by
  have h := checkLog_sound (w := (169247 / 1169247)) (n := 12)
    (lo := (291545101 / 1000000000)) (hi := (145772551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669247 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669247 / 500000) = 1/(500000 / 669247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13132 : Bounds (291545101 / 1000000000) (145772551 / 500000000) (Real.log (669247 / 500000)) := by
  have h := reflection_log_13132_neg
  have he : Real.log (669247 / 500000) = -Real.log (500000 / 669247) := by
    rw [show ((669247 / 500000) : ℝ) = ((500000 / 669247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13133_neg : (16529449 / 40000000) ≤ -Real.log (330753 / 500000) ∧
    -Real.log (330753 / 500000) ≤ (206618113 / 500000000) := by
  have h := checkLog_sound (w := (169247 / 830753)) (n := 12)
    (lo := (16529449 / 40000000)) (hi := (206618113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 330753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 330753) = 1/(330753 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13133 : Bounds (-206618113 / 500000000) (-16529449 / 40000000) (Real.log (330753 / 500000)) := by
  have h := reflection_log_13133_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13134_neg : (121691123 / 1000000000) ≤ -Real.log (221355452991 / 250000000000) ∧
    -Real.log (221355452991 / 250000000000) ≤ (30422781 / 250000000) := by
  have h := checkLog_sound (w := (28644547009 / 471355452991)) (n := 12)
    (lo := (121691123 / 1000000000)) (hi := (30422781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 221355452991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 221355452991) = 1/(221355452991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13134 : Bounds (-30422781 / 250000000) (-121691123 / 1000000000) (Real.log (221355452991 / 250000000000)) := by
  have h := reflection_log_13134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13135_neg : (29953377 / 250000000) ≤ -Real.log (887085855271 / 1000000000000) ∧
    -Real.log (887085855271 / 1000000000000) ≤ (119813509 / 1000000000) := by
  have h := checkLog_sound (w := (112914144729 / 1887085855271)) (n := 12)
    (lo := (29953377 / 250000000)) (hi := (119813509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 887085855271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 887085855271) = 1/(887085855271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13135 : Bounds (-119813509 / 1000000000) (-29953377 / 250000000) (Real.log (887085855271 / 1000000000000)) := by
  have h := reflection_log_13135_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13136_neg : (174803519 / 250000000) ≤ -Real.log (500000000000 / 1006085337807) ∧
    -Real.log (500000000000 / 1006085337807) ≤ (349607039 / 500000000) := by
  have h := checkLog_sound (w := (6085337807 / 2006085337807)) (n := 12)
    (lo := (379181 / 62500000)) (hi := (6066897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1006085337807 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1006085337807 / 1000000000000) = 1/(500000000000 / 1006085337807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13136 : Bounds (174803519 / 250000000) (349607039 / 500000000) (Real.log (1006085337807 / 500000000000)) := by
  have h := reflection_log_13136_neg
  have he : Real.log (1006085337807 / 500000000000) = -Real.log (500000000000 / 1006085337807) := by
    rw [show ((1006085337807 / 500000000000) : ℝ) = ((500000000000 / 1006085337807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13137_neg : (28191253 / 40000000) ≤ -Real.log (500000000000 / 1011702085847) ∧
    -Real.log (500000000000 / 1011702085847) ≤ (704781327 / 1000000000) := by
  have h := checkLog_sound (w := (11702085847 / 2011702085847)) (n := 12)
    (lo := (2326829 / 200000000)) (hi := (5817073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1011702085847 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1011702085847 / 1000000000000) = 1/(500000000000 / 1011702085847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13137 : Bounds (28191253 / 40000000) (704781327 / 1000000000) (Real.log (1011702085847 / 500000000000)) := by
  have h := reflection_log_13137_neg
  have he : Real.log (1011702085847 / 500000000000) = -Real.log (500000000000 / 1011702085847) := by
    rw [show ((1011702085847 / 500000000000) : ℝ) = ((500000000000 / 1011702085847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13138_neg : (729893189 / 500000000) ≤ -Real.log (500000000000 / 2152519893899) ∧
    -Real.log (500000000000 / 2152519893899) ≤ (1459786381 / 1000000000) := by
  have h := checkLog_sound (w := (152519893899 / 4152519893899)) (n := 12)
    (lo := (36746009 / 500000000)) (hi := (73492019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2152519893899 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2152519893899 / 2000000000000) = 1/(500000000000 / 2152519893899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13138 : Bounds (729893189 / 500000000) (1459786381 / 1000000000) (Real.log (2152519893899 / 500000000000)) := by
  have h := reflection_log_13138_neg
  have he : Real.log (2152519893899 / 500000000000) = -Real.log (500000000000 / 2152519893899) := by
    rw [show ((2152519893899 / 500000000000) : ℝ) = ((500000000000 / 2152519893899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13139_neg : (1469622491 / 1000000000) ≤ -Real.log (125000000000 / 543449197861) ∧
    -Real.log (125000000000 / 543449197861) ≤ (734811247 / 500000000) := by
  have h := checkLog_sound (w := (43449197861 / 1043449197861)) (n := 12)
    (lo := (83328131 / 1000000000)) (hi := (20832033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543449197861 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(543449197861 / 500000000000) = 1/(125000000000 / 543449197861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13139 : Bounds (1469622491 / 1000000000) (734811247 / 500000000) (Real.log (543449197861 / 125000000000)) := by
  have h := reflection_log_13139_neg
  have he : Real.log (543449197861 / 125000000000) = -Real.log (125000000000 / 543449197861) := by
    rw [show ((543449197861 / 125000000000) : ℝ) = ((125000000000 / 543449197861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13140_neg : (487966329 / 1000000000) ≤ -Real.log (1000 / 1629) ∧
    -Real.log (1000 / 1629) ≤ (48796633 / 100000000) := by
  have h := checkLog_sound (w := (629 / 2629)) (n := 12)
    (lo := (487966329 / 1000000000)) (hi := (48796633 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1629 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1629 / 1000) = 1/(1000 / 1629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13140 : Bounds (487966329 / 1000000000) (48796633 / 100000000) (Real.log (1629 / 1000)) := by
  have h := reflection_log_13140_neg
  have he : Real.log (1629 / 1000) = -Real.log (1000 / 1629) := by
    rw [show ((1629 / 1000) : ℝ) = ((1000 / 1629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13141_neg : (198310643 / 200000000) ≤ -Real.log (371 / 1000) ∧
    -Real.log (371 / 1000) ≤ (991553217 / 1000000000) := by
  have h := checkLog_sound (w := (129 / 871)) (n := 12)
    (lo := (59681207 / 200000000)) (hi := (74601509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 371) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 371) = 1/(371 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13141 : Bounds (-991553217 / 1000000000) (-198310643 / 200000000) (Real.log (371 / 1000)) := by
  have h := reflection_log_13141_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13142_neg : (314401 / 500000000) ≤ -Real.log (1000000 / 1000629) ∧
    -Real.log (1000000 / 1000629) ≤ (628803 / 1000000000) := by
  have h := checkLog_sound (w := (629 / 2000629)) (n := 12)
    (lo := (314401 / 500000000)) (hi := (628803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000629 / 1000000) = 1/(1000000 / 1000629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13142 : Bounds (314401 / 500000000) (628803 / 1000000000) (Real.log (1000629 / 1000000)) := by
  have h := reflection_log_13142_neg
  have he : Real.log (1000629 / 1000000) = -Real.log (1000000 / 1000629) := by
    rw [show ((1000629 / 1000000) : ℝ) = ((1000000 / 1000629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13143_neg : (629197 / 1000000000) ≤ -Real.log (999371 / 1000000) ∧
    -Real.log (999371 / 1000000) ≤ (314599 / 500000000) := by
  have h := checkLog_sound (w := (629 / 1999371)) (n := 12)
    (lo := (629197 / 1000000000)) (hi := (314599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999371) = 1/(999371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13143 : Bounds (-314599 / 500000000) (-629197 / 1000000000) (Real.log (999371 / 1000000)) := by
  have h := reflection_log_13143_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13144_neg : (291118411 / 1000000000) ≤ -Real.log (1000000 / 1337923) ∧
    -Real.log (1000000 / 1337923) ≤ (72779603 / 250000000) := by
  have h := checkLog_sound (w := (337923 / 2337923)) (n := 12)
    (lo := (291118411 / 1000000000)) (hi := (72779603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1337923 / 1000000) = 1/(1000000 / 1337923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13144 : Bounds (291118411 / 1000000000) (72779603 / 250000000) (Real.log (1337923 / 1000000)) := by
  have h := reflection_log_13144_neg
  have he : Real.log (1337923 / 1000000) = -Real.log (1000000 / 1337923) := by
    rw [show ((1337923 / 1000000) : ℝ) = ((1000000 / 1337923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13145_neg : (82474683 / 200000000) ≤ -Real.log (662077 / 1000000) ∧
    -Real.log (662077 / 1000000) ≤ (51546677 / 125000000) := by
  have h := checkLog_sound (w := (337923 / 1662077)) (n := 12)
    (lo := (82474683 / 200000000)) (hi := (51546677 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 662077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 662077) = 1/(662077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13145 : Bounds (-51546677 / 125000000) (-82474683 / 200000000) (Real.log (662077 / 1000000)) := by
  have h := reflection_log_13145_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13146_neg : (73241273 / 250000000) ≤ -Real.log (250000 / 335099) ∧
    -Real.log (250000 / 335099) ≤ (292965093 / 1000000000) := by
  have h := checkLog_sound (w := (85099 / 585099)) (n := 12)
    (lo := (73241273 / 250000000)) (hi := (292965093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335099 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335099 / 250000) = 1/(250000 / 335099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13146 : Bounds (73241273 / 250000000) (292965093 / 1000000000) (Real.log (335099 / 250000)) := by
  have h := reflection_log_13146_neg
  have he : Real.log (335099 / 250000) = -Real.log (250000 / 335099) := by
    rw [show ((335099 / 250000) : ℝ) = ((250000 / 335099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13147_neg : (52014453 / 125000000) ≤ -Real.log (164901 / 250000) ∧
    -Real.log (164901 / 250000) ≤ (133157 / 320000) := by
  have h := checkLog_sound (w := (85099 / 414901)) (n := 12)
    (lo := (52014453 / 125000000)) (hi := (133157 / 320000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 164901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 164901) = 1/(164901 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13147 : Bounds (-133157 / 320000) (-52014453 / 125000000) (Real.log (164901 / 250000)) := by
  have h := reflection_log_13147_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13148_neg : (123150531 / 1000000000) ≤ -Real.log (55258160199 / 62500000000) ∧
    -Real.log (55258160199 / 62500000000) ≤ (30787633 / 250000000) := by
  have h := checkLog_sound (w := (7241839801 / 117758160199)) (n := 12)
    (lo := (123150531 / 1000000000)) (hi := (30787633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 55258160199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 55258160199) = 1/(55258160199 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13148 : Bounds (-30787633 / 250000000) (-123150531 / 1000000000) (Real.log (55258160199 / 62500000000)) := by
  have h := reflection_log_13148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13149_neg : (30313751 / 250000000) ≤ -Real.log (885808046071 / 1000000000000) ∧
    -Real.log (885808046071 / 1000000000000) ≤ (24251001 / 200000000) := by
  have h := checkLog_sound (w := (114191953929 / 1885808046071)) (n := 12)
    (lo := (30313751 / 250000000)) (hi := (24251001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 885808046071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 885808046071) = 1/(885808046071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13149 : Bounds (-24251001 / 200000000) (-30313751 / 250000000) (Real.log (885808046071 / 1000000000000)) := by
  have h := reflection_log_13149_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13150_neg : (351745913 / 500000000) ≤ -Real.log (500000000000 / 1010398337353) ∧
    -Real.log (500000000000 / 1010398337353) ≤ (175872957 / 250000000) := by
  have h := checkLog_sound (w := (10398337353 / 2010398337353)) (n := 12)
    (lo := (5172323 / 500000000)) (hi := (10344647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1010398337353 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1010398337353 / 1000000000000) = 1/(500000000000 / 1010398337353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13150 : Bounds (351745913 / 500000000) (175872957 / 250000000) (Real.log (1010398337353 / 500000000000)) := by
  have h := reflection_log_13150_neg
  have he : Real.log (1010398337353 / 500000000000) = -Real.log (500000000000 / 1010398337353) := by
    rw [show ((1010398337353 / 500000000000) : ℝ) = ((500000000000 / 1010398337353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13151_neg : (177270179 / 250000000) ≤ -Real.log (500000000000 / 1016061151843) ∧
    -Real.log (500000000000 / 1016061151843) ≤ (354540359 / 500000000) := by
  have h := checkLog_sound (w := (16061151843 / 2016061151843)) (n := 12)
    (lo := (497923 / 31250000)) (hi := (15933537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1016061151843 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1016061151843 / 1000000000000) = 1/(500000000000 / 1016061151843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13151 : Bounds (177270179 / 250000000) (354540359 / 500000000) (Real.log (1016061151843 / 500000000000)) := by
  have h := reflection_log_13151_neg
  have he : Real.log (1016061151843 / 500000000000) = -Real.log (500000000000 / 1016061151843) := by
    rw [show ((1016061151843 / 500000000000) : ℝ) = ((500000000000 / 1016061151843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13152_neg : (1469622491 / 1000000000) ≤ -Real.log (500000000000 / 2173796791443) ∧
    -Real.log (500000000000 / 2173796791443) ≤ (734811247 / 500000000) := by
  have h := checkLog_sound (w := (173796791443 / 4173796791443)) (n := 12)
    (lo := (83328131 / 1000000000)) (hi := (20832033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2173796791443 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2173796791443 / 2000000000000) = 1/(500000000000 / 2173796791443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13152 : Bounds (1469622491 / 1000000000) (734811247 / 500000000) (Real.log (2173796791443 / 500000000000)) := by
  have h := reflection_log_13152_neg
  have he : Real.log (2173796791443 / 500000000000) = -Real.log (500000000000 / 2173796791443) := by
    rw [show ((2173796791443 / 500000000000) : ℝ) = ((500000000000 / 2173796791443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13153_neg : (184939943 / 125000000) ≤ -Real.log (250000000000 / 1097708894879) ∧
    -Real.log (250000000000 / 1097708894879) ≤ (1479519547 / 1000000000) := by
  have h := checkLog_sound (w := (97708894879 / 2097708894879)) (n := 12)
    (lo := (2913287 / 31250000)) (hi := (18645037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097708894879 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1097708894879 / 1000000000000) = 1/(250000000000 / 1097708894879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13153 : Bounds (184939943 / 125000000) (1479519547 / 1000000000) (Real.log (1097708894879 / 250000000000)) := by
  have h := reflection_log_13153_neg
  have he : Real.log (1097708894879 / 250000000000) = -Real.log (250000000000 / 1097708894879) := by
    rw [show ((1097708894879 / 250000000000) : ℝ) = ((250000000000 / 1097708894879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13154_neg : (30612891 / 62500000) ≤ -Real.log (125 / 204) ∧
    -Real.log (125 / 204) ≤ (489806257 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 329)) (n := 12)
    (lo := (30612891 / 62500000)) (hi := (489806257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204 / 125) = 1/(125 / 204) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13154 : Bounds (30612891 / 62500000) (489806257 / 1000000000) (Real.log (204 / 125)) := by
  have h := reflection_log_13154_neg
  have he : Real.log (204 / 125) = -Real.log (125 / 204) := by
    rw [show ((204 / 125) : ℝ) = ((125 / 204) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13155_neg : (49983617 / 50000000) ≤ -Real.log (46 / 125) ∧
    -Real.log (46 / 125) ≤ (499836171 / 500000000) := by
  have h := checkLog_sound (w := (33 / 217)) (n := 12)
    (lo := (7663129 / 25000000)) (hi := (306525161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 92) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 92) = 1/(46 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13155 : Bounds (-499836171 / 500000000) (-49983617 / 50000000) (Real.log (46 / 125)) := by
  have h := reflection_log_13155_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13156_neg : (3159 / 5000000) ≤ -Real.log (125000 / 125079) ∧
    -Real.log (125000 / 125079) ≤ (631801 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 250079)) (n := 12)
    (lo := (3159 / 5000000)) (hi := (631801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125079 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125079 / 125000) = 1/(125000 / 125079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13156 : Bounds (3159 / 5000000) (631801 / 1000000000) (Real.log (125079 / 125000)) := by
  have h := reflection_log_13156_neg
  have he : Real.log (125079 / 125000) = -Real.log (125000 / 125079) := by
    rw [show ((125079 / 125000) : ℝ) = ((125000 / 125079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13157_neg : (632199 / 1000000000) ≤ -Real.log (124921 / 125000) ∧
    -Real.log (124921 / 125000) ≤ (3161 / 5000000) := by
  have h := checkLog_sound (w := (79 / 249921)) (n := 12)
    (lo := (632199 / 1000000000)) (hi := (3161 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124921) = 1/(124921 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13157 : Bounds (-3161 / 5000000) (-632199 / 1000000000) (Real.log (124921 / 125000)) := by
  have h := reflection_log_13157_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13158_neg : (146269131 / 500000000) ≤ -Real.log (62500 / 83739) ∧
    -Real.log (62500 / 83739) ≤ (292538263 / 1000000000) := by
  have h := checkLog_sound (w := (21239 / 146239)) (n := 12)
    (lo := (146269131 / 500000000)) (hi := (292538263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83739 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83739 / 62500) = 1/(62500 / 83739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13158 : Bounds (146269131 / 500000000) (292538263 / 1000000000) (Real.log (83739 / 62500)) := by
  have h := reflection_log_13158_neg
  have he : Real.log (83739 / 62500) = -Real.log (62500 / 83739) := by
    rw [show ((83739 / 62500) : ℝ) = ((62500 / 83739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13159_neg : (103812203 / 250000000) ≤ -Real.log (41261 / 62500) ∧
    -Real.log (41261 / 62500) ≤ (415248813 / 1000000000) := by
  have h := checkLog_sound (w := (21239 / 103761)) (n := 12)
    (lo := (103812203 / 250000000)) (hi := (415248813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 41261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 41261) = 1/(41261 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13159 : Bounds (-415248813 / 1000000000) (-103812203 / 250000000) (Real.log (41261 / 62500)) := by
  have h := reflection_log_13159_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13160_neg : (14719377 / 50000000) ≤ -Real.log (31250 / 41947) ∧
    -Real.log (31250 / 41947) ≤ (294387541 / 1000000000) := by
  have h := checkLog_sound (w := (10697 / 73197)) (n := 12)
    (lo := (14719377 / 50000000)) (hi := (294387541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41947 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41947 / 31250) = 1/(31250 / 41947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13160 : Bounds (14719377 / 50000000) (294387541 / 1000000000) (Real.log (41947 / 31250)) := by
  have h := reflection_log_13160_neg
  have he : Real.log (41947 / 31250) = -Real.log (31250 / 41947) := by
    rw [show ((41947 / 31250) : ℝ) = ((31250 / 41947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13161_neg : (20950623 / 50000000) ≤ -Real.log (20553 / 31250) ∧
    -Real.log (20553 / 31250) ≤ (419012461 / 1000000000) := by
  have h := checkLog_sound (w := (10697 / 51803)) (n := 12)
    (lo := (20950623 / 50000000)) (hi := (419012461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 20553) = 1/(20553 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13161 : Bounds (-419012461 / 1000000000) (-20950623 / 50000000) (Real.log (20553 / 31250)) := by
  have h := reflection_log_13161_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13162_neg : (3115623 / 25000000) ≤ -Real.log (862136691 / 976562500) ∧
    -Real.log (862136691 / 976562500) ≤ (124624921 / 1000000000) := by
  have h := checkLog_sound (w := (114425809 / 1838699191)) (n := 12)
    (lo := (3115623 / 25000000)) (hi := (124624921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 862136691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 862136691) = 1/(862136691 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13162 : Bounds (-124624921 / 1000000000) (-3115623 / 25000000) (Real.log (862136691 / 976562500)) := by
  have h := reflection_log_13162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13163_neg : (2454211 / 20000000) ≤ -Real.log (3455154879 / 3906250000) ∧
    -Real.log (3455154879 / 3906250000) ≤ (122710551 / 1000000000) := by
  have h := checkLog_sound (w := (451095121 / 7361404879)) (n := 12)
    (lo := (2454211 / 20000000)) (hi := (122710551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3455154879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3455154879) = 1/(3455154879 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13163 : Bounds (-122710551 / 1000000000) (-2454211 / 20000000) (Real.log (3455154879 / 3906250000)) := by
  have h := reflection_log_13163_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13164_neg : (353893537 / 500000000) ≤ -Real.log (250000000000 / 507373791231) ∧
    -Real.log (250000000000 / 507373791231) ≤ (176946769 / 250000000) := by
  have h := checkLog_sound (w := (7373791231 / 1007373791231)) (n := 12)
    (lo := (7319947 / 500000000)) (hi := (2927979 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((507373791231 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(507373791231 / 500000000000) = 1/(250000000000 / 507373791231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13164 : Bounds (353893537 / 500000000) (176946769 / 250000000) (Real.log (507373791231 / 250000000000)) := by
  have h := reflection_log_13164_neg
  have he : Real.log (507373791231 / 250000000000) = -Real.log (250000000000 / 507373791231) := by
    rw [show ((507373791231 / 250000000000) : ℝ) = ((250000000000 / 507373791231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13165_neg : (3567 / 5000) ≤ -Real.log (250000000000 / 510229650173) ∧
    -Real.log (250000000000 / 510229650173) ≤ (356700001 / 500000000) := by
  have h := checkLog_sound (w := (10229650173 / 1010229650173)) (n := 12)
    (lo := (1012641 / 50000000)) (hi := (20252821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((510229650173 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(510229650173 / 500000000000) = 1/(250000000000 / 510229650173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13165 : Bounds (3567 / 5000) (356700001 / 500000000) (Real.log (510229650173 / 250000000000)) := by
  have h := reflection_log_13165_neg
  have he : Real.log (510229650173 / 250000000000) = -Real.log (250000000000 / 510229650173) := by
    rw [show ((510229650173 / 250000000000) : ℝ) = ((250000000000 / 510229650173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13166_neg : (184939943 / 125000000) ≤ -Real.log (500000000000 / 2195417789757) ∧
    -Real.log (500000000000 / 2195417789757) ≤ (1479519547 / 1000000000) := by
  have h := checkLog_sound (w := (195417789757 / 4195417789757)) (n := 12)
    (lo := (2913287 / 31250000)) (hi := (18645037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2195417789757 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2195417789757 / 2000000000000) = 1/(500000000000 / 2195417789757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13166 : Bounds (184939943 / 125000000) (1479519547 / 1000000000) (Real.log (2195417789757 / 500000000000)) := by
  have h := reflection_log_13166_neg
  have he : Real.log (2195417789757 / 500000000000) = -Real.log (500000000000 / 2195417789757) := by
    rw [show ((2195417789757 / 500000000000) : ℝ) = ((500000000000 / 2195417789757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13167_neg : (372369649 / 250000000) ≤ -Real.log (125000000000 / 554347826087) ∧
    -Real.log (125000000000 / 554347826087) ≤ (1489478599 / 1000000000) := by
  have h := checkLog_sound (w := (54347826087 / 1054347826087)) (n := 12)
    (lo := (25796059 / 250000000)) (hi := (103184237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((554347826087 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(554347826087 / 500000000000) = 1/(125000000000 / 554347826087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13167 : Bounds (372369649 / 250000000) (1489478599 / 1000000000) (Real.log (554347826087 / 125000000000)) := by
  have h := reflection_log_13167_neg
  have he : Real.log (554347826087 / 125000000000) = -Real.log (125000000000 / 554347826087) := by
    rw [show ((554347826087 / 125000000000) : ℝ) = ((125000000000 / 554347826087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13168_neg : (122910701 / 250000000) ≤ -Real.log (200 / 327) ∧
    -Real.log (200 / 327) ≤ (98328561 / 200000000) := by
  have h := checkLog_sound (w := (127 / 527)) (n := 12)
    (lo := (122910701 / 250000000)) (hi := (98328561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327 / 200) = 1/(200 / 327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13168 : Bounds (122910701 / 250000000) (98328561 / 200000000) (Real.log (327 / 200)) := by
  have h := reflection_log_13168_neg
  have he : Real.log (327 / 200) = -Real.log (200 / 327) := by
    rw [show ((327 / 200) : ℝ) = ((200 / 327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13169_neg : (251964481 / 250000000) ≤ -Real.log (73 / 200) ∧
    -Real.log (73 / 200) ≤ (503928963 / 500000000) := by
  have h := checkLog_sound (w := (27 / 173)) (n := 12)
    (lo := (39338843 / 125000000)) (hi := (62942149 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 73) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 73) = 1/(73 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13169 : Bounds (-503928963 / 500000000) (-251964481 / 250000000) (Real.log (73 / 200)) := by
  have h := reflection_log_13169_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13170_neg : (317399 / 500000000) ≤ -Real.log (200000 / 200127) ∧
    -Real.log (200000 / 200127) ≤ (634799 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 400127)) (n := 12)
    (lo := (317399 / 500000000)) (hi := (634799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200127 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200127 / 200000) = 1/(200000 / 200127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13170 : Bounds (317399 / 500000000) (634799 / 1000000000) (Real.log (200127 / 200000)) := by
  have h := reflection_log_13170_neg
  have he : Real.log (200127 / 200000) = -Real.log (200000 / 200127) := by
    rw [show ((200127 / 200000) : ℝ) = ((200000 / 200127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13171_neg : (635201 / 1000000000) ≤ -Real.log (199873 / 200000) ∧
    -Real.log (199873 / 200000) ≤ (317601 / 500000000) := by
  have h := checkLog_sound (w := (127 / 399873)) (n := 12)
    (lo := (635201 / 1000000000)) (hi := (317601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199873) = 1/(199873 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13171 : Bounds (-317601 / 500000000) (-635201 / 1000000000) (Real.log (199873 / 200000)) := by
  have h := reflection_log_13171_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13172_neg : (7348977 / 25000000) ≤ -Real.log (1000000 / 1341729) ∧
    -Real.log (1000000 / 1341729) ≤ (293959081 / 1000000000) := by
  have h := checkLog_sound (w := (341729 / 2341729)) (n := 12)
    (lo := (7348977 / 25000000)) (hi := (293959081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341729 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1341729 / 1000000) = 1/(1000000 / 1341729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13172 : Bounds (7348977 / 25000000) (293959081 / 1000000000) (Real.log (1341729 / 1000000)) := by
  have h := reflection_log_13172_neg
  have he : Real.log (1341729 / 1000000) = -Real.log (1000000 / 1341729) := by
    rw [show ((1341729 / 1000000) : ℝ) = ((1000000 / 1341729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13173_neg : (209069289 / 500000000) ≤ -Real.log (658271 / 1000000) ∧
    -Real.log (658271 / 1000000) ≤ (418138579 / 1000000000) := by
  have h := checkLog_sound (w := (341729 / 1658271)) (n := 12)
    (lo := (209069289 / 500000000)) (hi := (418138579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 658271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 658271) = 1/(658271 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13173 : Bounds (-418138579 / 1000000000) (-209069289 / 500000000) (Real.log (658271 / 1000000)) := by
  have h := reflection_log_13173_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13174_neg : (295810943 / 1000000000) ≤ -Real.log (125000 / 168027) ∧
    -Real.log (125000 / 168027) ≤ (2311023 / 7812500) := by
  have h := checkLog_sound (w := (43027 / 293027)) (n := 12)
    (lo := (295810943 / 1000000000)) (hi := (2311023 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168027 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168027 / 125000) = 1/(125000 / 168027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13174 : Bounds (295810943 / 1000000000) (2311023 / 7812500) (Real.log (168027 / 125000)) := by
  have h := reflection_log_13174_neg
  have he : Real.log (168027 / 125000) = -Real.log (125000 / 168027) := by
    rw [show ((168027 / 125000) : ℝ) = ((125000 / 168027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13175_neg : (105480953 / 250000000) ≤ -Real.log (81973 / 125000) ∧
    -Real.log (81973 / 125000) ≤ (421923813 / 1000000000) := by
  have h := checkLog_sound (w := (43027 / 206973)) (n := 12)
    (lo := (105480953 / 250000000)) (hi := (421923813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 81973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 81973) = 1/(81973 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13175 : Bounds (-421923813 / 1000000000) (-105480953 / 250000000) (Real.log (81973 / 125000)) := by
  have h := reflection_log_13175_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13176_neg : (126112869 / 1000000000) ≤ -Real.log (13773677271 / 15625000000) ∧
    -Real.log (13773677271 / 15625000000) ≤ (12611287 / 100000000) := by
  have h := checkLog_sound (w := (1851322729 / 29398677271)) (n := 12)
    (lo := (126112869 / 1000000000)) (hi := (12611287 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 13773677271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 13773677271) = 1/(13773677271 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13176 : Bounds (-12611287 / 100000000) (-126112869 / 1000000000) (Real.log (13773677271 / 15625000000)) := by
  have h := reflection_log_13176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13177_neg : (124179497 / 1000000000) ≤ -Real.log (883221290559 / 1000000000000) ∧
    -Real.log (883221290559 / 1000000000000) ≤ (62089749 / 500000000) := by
  have h := checkLog_sound (w := (116778709441 / 1883221290559)) (n := 12)
    (lo := (124179497 / 1000000000)) (hi := (62089749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 883221290559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 883221290559) = 1/(883221290559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13177 : Bounds (-62089749 / 500000000) (-124179497 / 1000000000) (Real.log (883221290559 / 1000000000000)) := by
  have h := reflection_log_13177_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13178_neg : (356048829 / 500000000) ≤ -Real.log (976562500 / 1990490583) ∧
    -Real.log (976562500 / 1990490583) ≤ (35604883 / 50000000) := by
  have h := checkLog_sound (w := (37365583 / 3943615583)) (n := 12)
    (lo := (9475239 / 500000000)) (hi := (18950479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1990490583 / 1953125000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1990490583 / 1953125000) = 1/(976562500 / 1990490583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13178 : Bounds (356048829 / 500000000) (35604883 / 50000000) (Real.log (1990490583 / 976562500)) := by
  have h := reflection_log_13178_neg
  have he : Real.log (1990490583 / 976562500) = -Real.log (976562500 / 1990490583) := by
    rw [show ((1990490583 / 976562500) : ℝ) = ((976562500 / 1990490583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13179_neg : (143546951 / 200000000) ≤ -Real.log (500000000000 / 1024892342601) ∧
    -Real.log (500000000000 / 1024892342601) ≤ (717734757 / 1000000000) := by
  have h := checkLog_sound (w := (24892342601 / 2024892342601)) (n := 12)
    (lo := (983503 / 40000000)) (hi := (3073447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024892342601 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1024892342601 / 1000000000000) = 1/(500000000000 / 1024892342601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13179 : Bounds (143546951 / 200000000) (717734757 / 1000000000) (Real.log (1024892342601 / 500000000000)) := by
  have h := reflection_log_13179_neg
  have he : Real.log (1024892342601 / 500000000000) = -Real.log (500000000000 / 1024892342601) := by
    rw [show ((1024892342601 / 500000000000) : ℝ) = ((500000000000 / 1024892342601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13180_neg : (372369649 / 250000000) ≤ -Real.log (500000000000 / 2217391304347) ∧
    -Real.log (500000000000 / 2217391304347) ≤ (1489478599 / 1000000000) := by
  have h := checkLog_sound (w := (217391304347 / 4217391304347)) (n := 12)
    (lo := (25796059 / 250000000)) (hi := (103184237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2217391304347 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2217391304347 / 2000000000000) = 1/(500000000000 / 2217391304347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13180 : Bounds (372369649 / 250000000) (1489478599 / 1000000000) (Real.log (2217391304347 / 500000000000)) := by
  have h := reflection_log_13180_neg
  have he : Real.log (2217391304347 / 500000000000) = -Real.log (500000000000 / 2217391304347) := by
    rw [show ((2217391304347 / 500000000000) : ℝ) = ((500000000000 / 2217391304347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13181_neg : (187437591 / 125000000) ≤ -Real.log (250000000000 / 1119863013699) ∧
    -Real.log (250000000000 / 1119863013699) ≤ (1499500731 / 1000000000) := by
  have h := checkLog_sound (w := (119863013699 / 2119863013699)) (n := 12)
    (lo := (3537699 / 31250000)) (hi := (113206369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1119863013699 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1119863013699 / 1000000000000) = 1/(250000000000 / 1119863013699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13181 : Bounds (187437591 / 125000000) (1499500731 / 1000000000) (Real.log (1119863013699 / 250000000000)) := by
  have h := reflection_log_13181_neg
  have he : Real.log (1119863013699 / 250000000000) = -Real.log (250000000000 / 1119863013699) := by
    rw [show ((1119863013699 / 250000000000) : ℝ) = ((250000000000 / 1119863013699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13182_neg : (98695197 / 200000000) ≤ -Real.log (500 / 819) ∧
    -Real.log (500 / 819) ≤ (246737993 / 500000000) := by
  have h := checkLog_sound (w := (319 / 1319)) (n := 12)
    (lo := (98695197 / 200000000)) (hi := (246737993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819 / 500) = 1/(500 / 819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13182 : Bounds (98695197 / 200000000) (246737993 / 500000000) (Real.log (819 / 500)) := by
  have h := reflection_log_13182_neg
  have he : Real.log (819 / 500) = -Real.log (500 / 819) := by
    rw [show ((819 / 500) : ℝ) = ((500 / 819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13183_neg : (508055533 / 500000000) ≤ -Real.log (181 / 500) ∧
    -Real.log (181 / 500) ≤ (254027767 / 250000000) := by
  have h := checkLog_sound (w := (69 / 431)) (n := 12)
    (lo := (161481943 / 500000000)) (hi := (322963887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 181) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 181) = 1/(181 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13183 : Bounds (-254027767 / 250000000) (-508055533 / 500000000) (Real.log (181 / 500)) := by
  have h := reflection_log_13183_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
