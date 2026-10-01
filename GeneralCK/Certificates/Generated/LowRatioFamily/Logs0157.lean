import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10048_neg : (35559959 / 200000000) ≤ -Real.log (83711 / 100000) ∧
    -Real.log (83711 / 100000) ≤ (44449949 / 250000000) := by
  have h := checkLog_sound (w := (16289 / 183711)) (n := 12)
    (lo := (35559959 / 200000000)) (hi := (44449949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 83711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 83711) = 1/(83711 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10048 : Bounds (-44449949 / 250000000) (-35559959 / 200000000) (Real.log (83711 / 100000)) := by
  have h := reflection_log_10048_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10049_neg : (758169 / 5000000) ≤ -Real.log (500000 / 581867) ∧
    -Real.log (500000 / 581867) ≤ (151633801 / 1000000000) := by
  have h := checkLog_sound (w := (81867 / 1081867)) (n := 12)
    (lo := (758169 / 5000000)) (hi := (151633801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581867 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581867 / 500000) = 1/(500000 / 581867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10049 : Bounds (758169 / 5000000) (151633801 / 1000000000) (Real.log (581867 / 500000)) := by
  have h := reflection_log_10049_neg
  have he : Real.log (581867 / 500000) = -Real.log (500000 / 581867) := by
    rw [show ((581867 / 500000) : ℝ) = ((500000 / 581867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10050_neg : (89404267 / 500000000) ≤ -Real.log (418133 / 500000) ∧
    -Real.log (418133 / 500000) ≤ (35761707 / 200000000) := by
  have h := checkLog_sound (w := (81867 / 918133)) (n := 12)
    (lo := (89404267 / 500000000)) (hi := (35761707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 418133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 418133) = 1/(418133 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10050 : Bounds (-35761707 / 200000000) (-89404267 / 500000000) (Real.log (418133 / 500000)) := by
  have h := reflection_log_10050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10051_neg : (27174733 / 1000000000) ≤ -Real.log (243297794311 / 250000000000) ∧
    -Real.log (243297794311 / 250000000000) ≤ (13587367 / 500000000) := by
  have h := checkLog_sound (w := (6702205689 / 493297794311)) (n := 12)
    (lo := (27174733 / 1000000000)) (hi := (13587367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243297794311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243297794311) = 1/(243297794311 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10051 : Bounds (-13587367 / 500000000) (-27174733 / 1000000000) (Real.log (243297794311 / 250000000000)) := by
  have h := reflection_log_10051_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10052_neg : (26891509 / 1000000000) ≤ -Real.log (9734668479 / 10000000000) ∧
    -Real.log (9734668479 / 10000000000) ≤ (2689151 / 100000000) := by
  have h := checkLog_sound (w := (265331521 / 19734668479)) (n := 12)
    (lo := (26891509 / 1000000000)) (hi := (2689151 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9734668479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9734668479) = 1/(9734668479 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10052 : Bounds (-2689151 / 100000000) (-26891509 / 1000000000) (Real.log (9734668479 / 10000000000)) := by
  have h := reflection_log_10052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10053_neg : (328708081 / 1000000000) ≤ -Real.log (500000000000 / 694586135633) ∧
    -Real.log (500000000000 / 694586135633) ≤ (164354041 / 500000000) := by
  have h := checkLog_sound (w := (194586135633 / 1194586135633)) (n := 12)
    (lo := (328708081 / 1000000000)) (hi := (164354041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694586135633 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694586135633 / 500000000000) = 1/(500000000000 / 694586135633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10053 : Bounds (328708081 / 1000000000) (164354041 / 500000000) (Real.log (694586135633 / 500000000000)) := by
  have h := reflection_log_10053_neg
  have he : Real.log (694586135633 / 500000000000) = -Real.log (500000000000 / 694586135633) := by
    rw [show ((694586135633 / 500000000000) : ℝ) = ((500000000000 / 694586135633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10054_neg : (66088467 / 200000000) ≤ -Real.log (100000000000 / 139158353921) ∧
    -Real.log (100000000000 / 139158353921) ≤ (10326323 / 31250000) := by
  have h := checkLog_sound (w := (39158353921 / 239158353921)) (n := 12)
    (lo := (66088467 / 200000000)) (hi := (10326323 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139158353921 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139158353921 / 100000000000) = 1/(100000000000 / 139158353921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10054 : Bounds (66088467 / 200000000) (10326323 / 31250000) (Real.log (139158353921 / 100000000000)) := by
  have h := reflection_log_10054_neg
  have he : Real.log (139158353921 / 100000000000) = -Real.log (100000000000 / 139158353921) := by
    rw [show ((139158353921 / 100000000000) : ℝ) = ((100000000000 / 139158353921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10055_neg : (663294217 / 1000000000) ≤ -Real.log (250000000000 / 485294117647) ∧
    -Real.log (250000000000 / 485294117647) ≤ (331647109 / 500000000) := by
  have h := checkLog_sound (w := (235294117647 / 735294117647)) (n := 12)
    (lo := (663294217 / 1000000000)) (hi := (331647109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((485294117647 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(485294117647 / 250000000000) = 1/(250000000000 / 485294117647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10055 : Bounds (663294217 / 1000000000) (331647109 / 500000000) (Real.log (485294117647 / 250000000000)) := by
  have h := reflection_log_10055_neg
  have he : Real.log (485294117647 / 250000000000) = -Real.log (250000000000 / 485294117647) := by
    rw [show ((485294117647 / 250000000000) : ℝ) = ((250000000000 / 485294117647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10056_neg : (83190397 / 125000000) ≤ -Real.log (250000000000 / 486377025037) ∧
    -Real.log (250000000000 / 486377025037) ≤ (665523177 / 1000000000) := by
  have h := checkLog_sound (w := (236377025037 / 736377025037)) (n := 12)
    (lo := (83190397 / 125000000)) (hi := (665523177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((486377025037 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(486377025037 / 250000000000) = 1/(250000000000 / 486377025037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10056 : Bounds (83190397 / 125000000) (665523177 / 1000000000) (Real.log (486377025037 / 250000000000)) := by
  have h := reflection_log_10056_neg
  have he : Real.log (486377025037 / 250000000000) = -Real.log (250000000000 / 486377025037) := by
    rw [show ((486377025037 / 250000000000) : ℝ) = ((250000000000 / 486377025037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10057_neg : (279145741 / 1000000000) ≤ -Real.log (500 / 661) ∧
    -Real.log (500 / 661) ≤ (139572871 / 500000000) := by
  have h := checkLog_sound (w := (161 / 1161)) (n := 12)
    (lo := (279145741 / 1000000000)) (hi := (139572871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661 / 500) = 1/(500 / 661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10057 : Bounds (279145741 / 1000000000) (139572871 / 500000000) (Real.log (661 / 500)) := by
  have h := reflection_log_10057_neg
  have he : Real.log (661 / 500) = -Real.log (500 / 661) := by
    rw [show ((661 / 500) : ℝ) = ((500 / 661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10058_neg : (388607991 / 1000000000) ≤ -Real.log (339 / 500) ∧
    -Real.log (339 / 500) ≤ (48575999 / 125000000) := by
  have h := checkLog_sound (w := (161 / 839)) (n := 12)
    (lo := (388607991 / 1000000000)) (hi := (48575999 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 339) = 1/(339 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10058 : Bounds (-48575999 / 125000000) (-388607991 / 1000000000) (Real.log (339 / 500)) := by
  have h := reflection_log_10058_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10059_neg : (80487 / 250000000) ≤ -Real.log (500000 / 500161) ∧
    -Real.log (500000 / 500161) ≤ (321949 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1000161)) (n := 12)
    (lo := (80487 / 250000000)) (hi := (321949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500161 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500161 / 500000) = 1/(500000 / 500161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10059 : Bounds (80487 / 250000000) (321949 / 1000000000) (Real.log (500161 / 500000)) := by
  have h := reflection_log_10059_neg
  have he : Real.log (500161 / 500000) = -Real.log (500000 / 500161) := by
    rw [show ((500161 / 500000) : ℝ) = ((500000 / 500161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10060_neg : (322051 / 1000000000) ≤ -Real.log (499839 / 500000) ∧
    -Real.log (499839 / 500000) ≤ (80513 / 250000000) := by
  have h := checkLog_sound (w := (161 / 999839)) (n := 12)
    (lo := (322051 / 1000000000)) (hi := (80513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499839) = 1/(499839 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10060 : Bounds (-80513 / 250000000) (-322051 / 1000000000) (Real.log (499839 / 500000)) := by
  have h := reflection_log_10060_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10061_neg : (9460139 / 62500000) ≤ -Real.log (500000 / 581709) ∧
    -Real.log (500000 / 581709) ≤ (6054489 / 40000000) := by
  have h := checkLog_sound (w := (81709 / 1081709)) (n := 12)
    (lo := (9460139 / 62500000)) (hi := (6054489 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581709 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581709 / 500000) = 1/(500000 / 581709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10061 : Bounds (9460139 / 62500000) (6054489 / 40000000) (Real.log (581709 / 500000)) := by
  have h := reflection_log_10061_neg
  have he : Real.log (581709 / 500000) = -Real.log (500000 / 581709) := by
    rw [show ((581709 / 500000) : ℝ) = ((500000 / 581709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10062_neg : (35686147 / 200000000) ≤ -Real.log (418291 / 500000) ∧
    -Real.log (418291 / 500000) ≤ (11151921 / 62500000) := by
  have h := checkLog_sound (w := (81709 / 918291)) (n := 12)
    (lo := (35686147 / 200000000)) (hi := (11151921 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 418291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 418291) = 1/(418291 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10062 : Bounds (-11151921 / 62500000) (-35686147 / 200000000) (Real.log (418291 / 500000)) := by
  have h := reflection_log_10062_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10063_neg : (152089127 / 1000000000) ≤ -Real.log (125000 / 145533) ∧
    -Real.log (125000 / 145533) ≤ (19011141 / 125000000) := by
  have h := checkLog_sound (w := (20533 / 270533)) (n := 12)
    (lo := (152089127 / 1000000000)) (hi := (19011141 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145533 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145533 / 125000) = 1/(125000 / 145533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10063 : Bounds (152089127 / 1000000000) (19011141 / 125000000) (Real.log (145533 / 125000)) := by
  have h := reflection_log_10063_neg
  have he : Real.log (145533 / 125000) = -Real.log (125000 / 145533) := by
    rw [show ((145533 / 125000) : ℝ) = ((125000 / 145533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10064_neg : (35888501 / 200000000) ≤ -Real.log (104467 / 125000) ∧
    -Real.log (104467 / 125000) ≤ (89721253 / 500000000) := by
  have h := checkLog_sound (w := (20533 / 229467)) (n := 12)
    (lo := (35888501 / 200000000)) (hi := (89721253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104467) = 1/(104467 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10064 : Bounds (-89721253 / 500000000) (-35888501 / 200000000) (Real.log (104467 / 125000)) := by
  have h := reflection_log_10064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10065_neg : (27353377 / 1000000000) ≤ -Real.log (15203395911 / 15625000000) ∧
    -Real.log (15203395911 / 15625000000) ≤ (13676689 / 500000000) := by
  have h := checkLog_sound (w := (421604089 / 30828395911)) (n := 12)
    (lo := (27353377 / 1000000000)) (hi := (13676689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15203395911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15203395911) = 1/(15203395911 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10065 : Bounds (-13676689 / 500000000) (-27353377 / 1000000000) (Real.log (15203395911 / 15625000000)) := by
  have h := reflection_log_10065_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10066_neg : (27068511 / 1000000000) ≤ -Real.log (243323639319 / 250000000000) ∧
    -Real.log (243323639319 / 250000000000) ≤ (845891 / 31250000) := by
  have h := checkLog_sound (w := (6676360681 / 493323639319)) (n := 12)
    (lo := (27068511 / 1000000000)) (hi := (845891 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243323639319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243323639319) = 1/(243323639319 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10066 : Bounds (-845891 / 31250000) (-27068511 / 1000000000) (Real.log (243323639319 / 250000000000)) := by
  have h := reflection_log_10066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10067_neg : (1030603 / 3125000) ≤ -Real.log (500000000000 / 695340086207) ∧
    -Real.log (500000000000 / 695340086207) ≤ (329792961 / 1000000000) := by
  have h := checkLog_sound (w := (195340086207 / 1195340086207)) (n := 12)
    (lo := (1030603 / 3125000)) (hi := (329792961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695340086207 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695340086207 / 500000000000) = 1/(500000000000 / 695340086207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10067 : Bounds (1030603 / 3125000) (329792961 / 1000000000) (Real.log (695340086207 / 500000000000)) := by
  have h := reflection_log_10067_neg
  have he : Real.log (695340086207 / 500000000000) = -Real.log (500000000000 / 695340086207) := by
    rw [show ((695340086207 / 500000000000) : ℝ) = ((500000000000 / 695340086207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10068_neg : (20720727 / 62500000) ≤ -Real.log (500000000000 / 696550106733) ∧
    -Real.log (500000000000 / 696550106733) ≤ (331531633 / 1000000000) := by
  have h := checkLog_sound (w := (196550106733 / 1196550106733)) (n := 12)
    (lo := (20720727 / 62500000)) (hi := (331531633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696550106733 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696550106733 / 500000000000) = 1/(500000000000 / 696550106733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10068 : Bounds (20720727 / 62500000) (331531633 / 1000000000) (Real.log (696550106733 / 500000000000)) := by
  have h := reflection_log_10068_neg
  have he : Real.log (696550106733 / 500000000000) = -Real.log (500000000000 / 696550106733) := by
    rw [show ((696550106733 / 500000000000) : ℝ) = ((500000000000 / 696550106733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10069_neg : (83190397 / 125000000) ≤ -Real.log (500000000000 / 972754050073) ∧
    -Real.log (500000000000 / 972754050073) ≤ (665523177 / 1000000000) := by
  have h := checkLog_sound (w := (472754050073 / 1472754050073)) (n := 12)
    (lo := (83190397 / 125000000)) (hi := (665523177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972754050073 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972754050073 / 500000000000) = 1/(500000000000 / 972754050073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10069 : Bounds (83190397 / 125000000) (665523177 / 1000000000) (Real.log (972754050073 / 500000000000)) := by
  have h := reflection_log_10069_neg
  have he : Real.log (972754050073 / 500000000000) = -Real.log (500000000000 / 972754050073) := by
    rw [show ((972754050073 / 500000000000) : ℝ) = ((500000000000 / 972754050073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10070_neg : (166938433 / 250000000) ≤ -Real.log (62500000000 / 121865781711) ∧
    -Real.log (62500000000 / 121865781711) ≤ (667753733 / 1000000000) := by
  have h := checkLog_sound (w := (59365781711 / 184365781711)) (n := 12)
    (lo := (166938433 / 250000000)) (hi := (667753733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121865781711 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121865781711 / 62500000000) = 1/(62500000000 / 121865781711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10070 : Bounds (166938433 / 250000000) (667753733 / 1000000000) (Real.log (121865781711 / 62500000000)) := by
  have h := reflection_log_10070_neg
  have he : Real.log (121865781711 / 62500000000) = -Real.log (62500000000 / 121865781711) := by
    rw [show ((121865781711 / 62500000000) : ℝ) = ((62500000000 / 121865781711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10071_neg : (55980377 / 200000000) ≤ -Real.log (1000 / 1323) ∧
    -Real.log (1000 / 1323) ≤ (139950943 / 500000000) := by
  have h := checkLog_sound (w := (323 / 2323)) (n := 12)
    (lo := (55980377 / 200000000)) (hi := (139950943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1323 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1323 / 1000) = 1/(1000 / 1323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10071 : Bounds (55980377 / 200000000) (139950943 / 500000000) (Real.log (1323 / 1000)) := by
  have h := reflection_log_10071_neg
  have he : Real.log (1323 / 1000) = -Real.log (1000 / 1323) := by
    rw [show ((1323 / 1000) : ℝ) = ((1000 / 1323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10072_neg : (195042003 / 500000000) ≤ -Real.log (677 / 1000) ∧
    -Real.log (677 / 1000) ≤ (390084007 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 1677)) (n := 12)
    (lo := (195042003 / 500000000)) (hi := (390084007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 677) = 1/(677 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10072 : Bounds (-390084007 / 1000000000) (-195042003 / 500000000) (Real.log (677 / 1000)) := by
  have h := reflection_log_10072_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10073_neg : (322947 / 1000000000) ≤ -Real.log (1000000 / 1000323) ∧
    -Real.log (1000000 / 1000323) ≤ (80737 / 250000000) := by
  have h := checkLog_sound (w := (323 / 2000323)) (n := 12)
    (lo := (322947 / 1000000000)) (hi := (80737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000323 / 1000000) = 1/(1000000 / 1000323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10073 : Bounds (322947 / 1000000000) (80737 / 250000000) (Real.log (1000323 / 1000000)) := by
  have h := reflection_log_10073_neg
  have he : Real.log (1000323 / 1000000) = -Real.log (1000000 / 1000323) := by
    rw [show ((1000323 / 1000000) : ℝ) = ((1000000 / 1000323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10074_neg : (80763 / 250000000) ≤ -Real.log (999677 / 1000000) ∧
    -Real.log (999677 / 1000000) ≤ (323053 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 1999677)) (n := 12)
    (lo := (80763 / 250000000)) (hi := (323053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999677) = 1/(999677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10074 : Bounds (-323053 / 1000000000) (-80763 / 250000000) (Real.log (999677 / 1000000)) := by
  have h := reflection_log_10074_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10075_neg : (30363363 / 200000000) ≤ -Real.log (1000000 / 1163947) ∧
    -Real.log (1000000 / 1163947) ≤ (9488551 / 62500000) := by
  have h := checkLog_sound (w := (163947 / 2163947)) (n := 12)
    (lo := (30363363 / 200000000)) (hi := (9488551 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1163947 / 1000000) = 1/(1000000 / 1163947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10075 : Bounds (30363363 / 200000000) (9488551 / 62500000) (Real.log (1163947 / 1000000)) := by
  have h := reflection_log_10075_neg
  have he : Real.log (1163947 / 1000000) = -Real.log (1000000 / 1163947) := by
    rw [show ((1163947 / 1000000) : ℝ) = ((1000000 / 1163947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10076_neg : (17906327 / 100000000) ≤ -Real.log (836053 / 1000000) ∧
    -Real.log (836053 / 1000000) ≤ (179063271 / 1000000000) := by
  have h := checkLog_sound (w := (163947 / 1836053)) (n := 12)
    (lo := (17906327 / 100000000)) (hi := (179063271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 836053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 836053) = 1/(836053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10076 : Bounds (-179063271 / 1000000000) (-17906327 / 100000000) (Real.log (836053 / 1000000)) := by
  have h := reflection_log_10076_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10077_neg : (152544247 / 1000000000) ≤ -Real.log (500000 / 582397) ∧
    -Real.log (500000 / 582397) ≤ (19068031 / 125000000) := by
  have h := checkLog_sound (w := (82397 / 1082397)) (n := 12)
    (lo := (152544247 / 1000000000)) (hi := (19068031 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582397 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582397 / 500000) = 1/(500000 / 582397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10077 : Bounds (152544247 / 1000000000) (19068031 / 125000000) (Real.log (582397 / 500000)) := by
  have h := reflection_log_10077_neg
  have he : Real.log (582397 / 500000) = -Real.log (500000 / 582397) := by
    rw [show ((582397 / 500000) : ℝ) = ((500000 / 582397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10078_neg : (180076877 / 1000000000) ≤ -Real.log (417603 / 500000) ∧
    -Real.log (417603 / 500000) ≤ (90038439 / 500000000) := by
  have h := checkLog_sound (w := (82397 / 917603)) (n := 12)
    (lo := (180076877 / 1000000000)) (hi := (90038439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 417603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 417603) = 1/(417603 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10078 : Bounds (-90038439 / 500000000) (-180076877 / 1000000000) (Real.log (417603 / 500000)) := by
  have h := reflection_log_10078_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10079_neg : (2753263 / 100000000) ≤ -Real.log (243210734391 / 250000000000) ∧
    -Real.log (243210734391 / 250000000000) ≤ (27532631 / 1000000000) := by
  have h := checkLog_sound (w := (6789265609 / 493210734391)) (n := 12)
    (lo := (2753263 / 100000000)) (hi := (27532631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243210734391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243210734391) = 1/(243210734391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10079 : Bounds (-27532631 / 1000000000) (-2753263 / 100000000) (Real.log (243210734391 / 250000000000)) := by
  have h := reflection_log_10079_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10080_neg : (5449291 / 200000000) ≤ -Real.log (973121381191 / 1000000000000) ∧
    -Real.log (973121381191 / 1000000000000) ≤ (3405807 / 125000000) := by
  have h := checkLog_sound (w := (26878618809 / 1973121381191)) (n := 12)
    (lo := (5449291 / 200000000)) (hi := (3405807 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973121381191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973121381191) = 1/(973121381191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10080 : Bounds (-3405807 / 125000000) (-5449291 / 200000000) (Real.log (973121381191 / 1000000000000)) := by
  have h := reflection_log_10080_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10081_neg : (165440043 / 500000000) ≤ -Real.log (125000000000 / 174024104931) ∧
    -Real.log (125000000000 / 174024104931) ≤ (330880087 / 1000000000) := by
  have h := checkLog_sound (w := (49024104931 / 299024104931)) (n := 12)
    (lo := (165440043 / 500000000)) (hi := (330880087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174024104931 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174024104931 / 125000000000) = 1/(125000000000 / 174024104931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10081 : Bounds (165440043 / 500000000) (330880087 / 1000000000) (Real.log (174024104931 / 125000000000)) := by
  have h := reflection_log_10081_neg
  have he : Real.log (174024104931 / 125000000000) = -Real.log (125000000000 / 174024104931) := by
    rw [show ((174024104931 / 125000000000) : ℝ) = ((125000000000 / 174024104931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10082_neg : (2660969 / 8000000) ≤ -Real.log (500000000000 / 697309406303) ∧
    -Real.log (500000000000 / 697309406303) ≤ (166310563 / 500000000) := by
  have h := checkLog_sound (w := (197309406303 / 1197309406303)) (n := 12)
    (lo := (2660969 / 8000000)) (hi := (166310563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697309406303 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697309406303 / 500000000000) = 1/(500000000000 / 697309406303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10082 : Bounds (2660969 / 8000000) (166310563 / 500000000) (Real.log (697309406303 / 500000000000)) := by
  have h := reflection_log_10082_neg
  have he : Real.log (697309406303 / 500000000000) = -Real.log (500000000000 / 697309406303) := by
    rw [show ((697309406303 / 500000000000) : ℝ) = ((500000000000 / 697309406303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10083_neg : (166938433 / 250000000) ≤ -Real.log (500000000000 / 974926253687) ∧
    -Real.log (500000000000 / 974926253687) ≤ (667753733 / 1000000000) := by
  have h := checkLog_sound (w := (474926253687 / 1474926253687)) (n := 12)
    (lo := (166938433 / 250000000)) (hi := (667753733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974926253687 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(974926253687 / 500000000000) = 1/(500000000000 / 974926253687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10083 : Bounds (166938433 / 250000000) (667753733 / 1000000000) (Real.log (974926253687 / 500000000000)) := by
  have h := reflection_log_10083_neg
  have he : Real.log (974926253687 / 500000000000) = -Real.log (500000000000 / 974926253687) := by
    rw [show ((974926253687 / 500000000000) : ℝ) = ((500000000000 / 974926253687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10084_neg : (669985891 / 1000000000) ≤ -Real.log (500000000000 / 977104874447) ∧
    -Real.log (500000000000 / 977104874447) ≤ (167496473 / 250000000) := by
  have h := checkLog_sound (w := (477104874447 / 1477104874447)) (n := 12)
    (lo := (669985891 / 1000000000)) (hi := (167496473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977104874447 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977104874447 / 500000000000) = 1/(500000000000 / 977104874447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10084 : Bounds (669985891 / 1000000000) (167496473 / 250000000) (Real.log (977104874447 / 500000000000)) := by
  have h := reflection_log_10084_neg
  have he : Real.log (977104874447 / 500000000000) = -Real.log (500000000000 / 977104874447) := by
    rw [show ((977104874447 / 500000000000) : ℝ) = ((500000000000 / 977104874447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10085_neg : (280657457 / 1000000000) ≤ -Real.log (250 / 331) ∧
    -Real.log (250 / 331) ≤ (140328729 / 500000000) := by
  have h := checkLog_sound (w := (81 / 581)) (n := 12)
    (lo := (280657457 / 1000000000)) (hi := (140328729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((331 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(331 / 250) = 1/(250 / 331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10085 : Bounds (280657457 / 1000000000) (140328729 / 500000000) (Real.log (331 / 250)) := by
  have h := reflection_log_10085_neg
  have he : Real.log (331 / 250) = -Real.log (250 / 331) := by
    rw [show ((331 / 250) : ℝ) = ((250 / 331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10086_neg : (195781101 / 500000000) ≤ -Real.log (169 / 250) ∧
    -Real.log (169 / 250) ≤ (391562203 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 419)) (n := 12)
    (lo := (195781101 / 500000000)) (hi := (391562203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 169) = 1/(169 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10086 : Bounds (-391562203 / 1000000000) (-195781101 / 500000000) (Real.log (169 / 250)) := by
  have h := reflection_log_10086_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10087_neg : (323947 / 1000000000) ≤ -Real.log (250000 / 250081) ∧
    -Real.log (250000 / 250081) ≤ (80987 / 250000000) := by
  have h := checkLog_sound (w := (81 / 500081)) (n := 12)
    (lo := (323947 / 1000000000)) (hi := (80987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250081 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250081 / 250000) = 1/(250000 / 250081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10087 : Bounds (323947 / 1000000000) (80987 / 250000000) (Real.log (250081 / 250000)) := by
  have h := reflection_log_10087_neg
  have he : Real.log (250081 / 250000) = -Real.log (250000 / 250081) := by
    rw [show ((250081 / 250000) : ℝ) = ((250000 / 250081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10088_neg : (81013 / 250000000) ≤ -Real.log (249919 / 250000) ∧
    -Real.log (249919 / 250000) ≤ (324053 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 499919)) (n := 12)
    (lo := (81013 / 250000000)) (hi := (324053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249919) = 1/(249919 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10088 : Bounds (-324053 / 1000000000) (-81013 / 250000000) (Real.log (249919 / 250000)) := by
  have h := reflection_log_10088_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10089_neg : (152272059 / 1000000000) ≤ -Real.log (1000000 / 1164477) ∧
    -Real.log (1000000 / 1164477) ≤ (7613603 / 50000000) := by
  have h := checkLog_sound (w := (164477 / 2164477)) (n := 12)
    (lo := (152272059 / 1000000000)) (hi := (7613603 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1164477 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1164477 / 1000000) = 1/(1000000 / 1164477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10089 : Bounds (152272059 / 1000000000) (7613603 / 50000000) (Real.log (1164477 / 1000000)) := by
  have h := reflection_log_10089_neg
  have he : Real.log (1164477 / 1000000) = -Real.log (1000000 / 1164477) := by
    rw [show ((1164477 / 1000000) : ℝ) = ((1000000 / 1164477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10090_neg : (89848701 / 500000000) ≤ -Real.log (835523 / 1000000) ∧
    -Real.log (835523 / 1000000) ≤ (179697403 / 1000000000) := by
  have h := checkLog_sound (w := (164477 / 1835523)) (n := 12)
    (lo := (89848701 / 500000000)) (hi := (179697403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 835523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 835523) = 1/(835523 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10090 : Bounds (-179697403 / 1000000000) (-89848701 / 500000000) (Real.log (835523 / 1000000)) := by
  have h := reflection_log_10090_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10091_neg : (76500009 / 500000000) ≤ -Real.log (40000 / 46613) ∧
    -Real.log (40000 / 46613) ≤ (153000019 / 1000000000) := by
  have h := checkLog_sound (w := (6613 / 86613)) (n := 12)
    (lo := (76500009 / 500000000)) (hi := (153000019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46613 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46613 / 40000) = 1/(40000 / 46613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10091 : Bounds (76500009 / 500000000) (153000019 / 1000000000) (Real.log (46613 / 40000)) := by
  have h := reflection_log_10091_neg
  have he : Real.log (46613 / 40000) = -Real.log (40000 / 46613) := by
    rw [show ((46613 / 40000) : ℝ) = ((40000 / 46613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10092_neg : (180712851 / 1000000000) ≤ -Real.log (33387 / 40000) ∧
    -Real.log (33387 / 40000) ≤ (45178213 / 250000000) := by
  have h := checkLog_sound (w := (6613 / 73387)) (n := 12)
    (lo := (180712851 / 1000000000)) (hi := (45178213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 33387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 33387) = 1/(33387 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10092 : Bounds (-45178213 / 250000000) (-180712851 / 1000000000) (Real.log (33387 / 40000)) := by
  have h := reflection_log_10092_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10093_neg : (27712833 / 1000000000) ≤ -Real.log (1556268231 / 1600000000) ∧
    -Real.log (1556268231 / 1600000000) ≤ (13856417 / 500000000) := by
  have h := checkLog_sound (w := (43731769 / 3156268231)) (n := 12)
    (lo := (27712833 / 1000000000)) (hi := (13856417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1556268231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1556268231) = 1/(1556268231 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10093 : Bounds (-13856417 / 500000000) (-27712833 / 1000000000) (Real.log (1556268231 / 1600000000)) := by
  have h := reflection_log_10093_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10094_neg : (27425343 / 1000000000) ≤ -Real.log (972947316471 / 1000000000000) ∧
    -Real.log (972947316471 / 1000000000000) ≤ (428521 / 15625000) := by
  have h := checkLog_sound (w := (27052683529 / 1972947316471)) (n := 12)
    (lo := (27425343 / 1000000000)) (hi := (428521 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972947316471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972947316471) = 1/(972947316471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10094 : Bounds (-428521 / 15625000) (-27425343 / 1000000000) (Real.log (972947316471 / 1000000000000)) := by
  have h := reflection_log_10094_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10095_neg : (165984731 / 500000000) ≤ -Real.log (20000000000 / 27874205737) ∧
    -Real.log (20000000000 / 27874205737) ≤ (331969463 / 1000000000) := by
  have h := checkLog_sound (w := (7874205737 / 47874205737)) (n := 12)
    (lo := (165984731 / 500000000)) (hi := (331969463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27874205737 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27874205737 / 20000000000) = 1/(20000000000 / 27874205737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10095 : Bounds (165984731 / 500000000) (331969463 / 1000000000) (Real.log (27874205737 / 20000000000)) := by
  have h := reflection_log_10095_neg
  have he : Real.log (27874205737 / 20000000000) = -Real.log (20000000000 / 27874205737) := by
    rw [show ((27874205737 / 20000000000) : ℝ) = ((20000000000 / 27874205737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10096_neg : (333712869 / 1000000000) ≤ -Real.log (500000000000 / 698071105521) ∧
    -Real.log (500000000000 / 698071105521) ≤ (33371287 / 100000000) := by
  have h := checkLog_sound (w := (198071105521 / 1198071105521)) (n := 12)
    (lo := (333712869 / 1000000000)) (hi := (33371287 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698071105521 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698071105521 / 500000000000) = 1/(500000000000 / 698071105521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10096 : Bounds (333712869 / 1000000000) (33371287 / 100000000) (Real.log (698071105521 / 500000000000)) := by
  have h := reflection_log_10096_neg
  have he : Real.log (698071105521 / 500000000000) = -Real.log (500000000000 / 698071105521) := by
    rw [show ((698071105521 / 500000000000) : ℝ) = ((500000000000 / 698071105521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10097_neg : (669985891 / 1000000000) ≤ -Real.log (250000000000 / 488552437223) ∧
    -Real.log (250000000000 / 488552437223) ≤ (167496473 / 250000000) := by
  have h := checkLog_sound (w := (238552437223 / 738552437223)) (n := 12)
    (lo := (669985891 / 1000000000)) (hi := (167496473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((488552437223 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(488552437223 / 250000000000) = 1/(250000000000 / 488552437223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10097 : Bounds (669985891 / 1000000000) (167496473 / 250000000) (Real.log (488552437223 / 250000000000)) := by
  have h := reflection_log_10097_neg
  have he : Real.log (488552437223 / 250000000000) = -Real.log (250000000000 / 488552437223) := by
    rw [show ((488552437223 / 250000000000) : ℝ) = ((250000000000 / 488552437223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10098_neg : (33610983 / 50000000) ≤ -Real.log (500000000000 / 979289940829) ∧
    -Real.log (500000000000 / 979289940829) ≤ (672219661 / 1000000000) := by
  have h := checkLog_sound (w := (479289940829 / 1479289940829)) (n := 12)
    (lo := (33610983 / 50000000)) (hi := (672219661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((979289940829 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(979289940829 / 500000000000) = 1/(500000000000 / 979289940829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10098 : Bounds (33610983 / 50000000) (672219661 / 1000000000) (Real.log (979289940829 / 500000000000)) := by
  have h := reflection_log_10098_neg
  have he : Real.log (979289940829 / 500000000000) = -Real.log (500000000000 / 979289940829) := by
    rw [show ((979289940829 / 500000000000) : ℝ) = ((500000000000 / 979289940829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10099_neg : (281412459 / 1000000000) ≤ -Real.log (40 / 53) ∧
    -Real.log (40 / 53) ≤ (14070623 / 50000000) := by
  have h := checkLog_sound (w := (13 / 93)) (n := 12)
    (lo := (281412459 / 1000000000)) (hi := (14070623 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53 / 40) = 1/(40 / 53) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10099 : Bounds (281412459 / 1000000000) (14070623 / 50000000) (Real.log (53 / 40)) := by
  have h := reflection_log_10099_neg
  have he : Real.log (53 / 40) = -Real.log (40 / 53) := by
    rw [show ((53 / 40) : ℝ) = ((40 / 53) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10100_neg : (98260647 / 250000000) ≤ -Real.log (27 / 40) ∧
    -Real.log (27 / 40) ≤ (393042589 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 27) = 1/(27 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10100 : Bounds (-393042589 / 1000000000) (-98260647 / 250000000) (Real.log (27 / 40)) := by
  have h := reflection_log_10100_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10101_neg : (324947 / 1000000000) ≤ -Real.log (40000 / 40013) ∧
    -Real.log (40000 / 40013) ≤ (81237 / 250000000) := by
  have h := checkLog_sound (w := (13 / 80013)) (n := 12)
    (lo := (324947 / 1000000000)) (hi := (81237 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40013 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40013 / 40000) = 1/(40000 / 40013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10101 : Bounds (324947 / 1000000000) (81237 / 250000000) (Real.log (40013 / 40000)) := by
  have h := reflection_log_10101_neg
  have he : Real.log (40013 / 40000) = -Real.log (40000 / 40013) := by
    rw [show ((40013 / 40000) : ℝ) = ((40000 / 40013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10102_neg : (81263 / 250000000) ≤ -Real.log (39987 / 40000) ∧
    -Real.log (39987 / 40000) ≤ (325053 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 79987)) (n := 12)
    (lo := (81263 / 250000000)) (hi := (325053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39987) = 1/(39987 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10102 : Bounds (-325053 / 1000000000) (-81263 / 250000000) (Real.log (39987 / 40000)) := by
  have h := reflection_log_10102_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10103_neg : (152726237 / 1000000000) ≤ -Real.log (500000 / 582503) ∧
    -Real.log (500000 / 582503) ≤ (76363119 / 500000000) := by
  have h := checkLog_sound (w := (82503 / 1082503)) (n := 12)
    (lo := (152726237 / 1000000000)) (hi := (76363119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582503 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582503 / 500000) = 1/(500000 / 582503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10103 : Bounds (152726237 / 1000000000) (76363119 / 500000000) (Real.log (582503 / 500000)) := by
  have h := reflection_log_10103_neg
  have he : Real.log (582503 / 500000) = -Real.log (500000 / 582503) := by
    rw [show ((582503 / 500000) : ℝ) = ((500000 / 582503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10104_neg : (180330739 / 1000000000) ≤ -Real.log (417497 / 500000) ∧
    -Real.log (417497 / 500000) ≤ (9016537 / 50000000) := by
  have h := checkLog_sound (w := (82503 / 917497)) (n := 12)
    (lo := (180330739 / 1000000000)) (hi := (9016537 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 417497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 417497) = 1/(417497 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10104 : Bounds (-9016537 / 50000000) (-180330739 / 1000000000) (Real.log (417497 / 500000)) := by
  have h := reflection_log_10104_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10105_neg : (153454723 / 1000000000) ≤ -Real.log (200000 / 233171) ∧
    -Real.log (200000 / 233171) ≤ (38363681 / 250000000) := by
  have h := checkLog_sound (w := (33171 / 433171)) (n := 12)
    (lo := (153454723 / 1000000000)) (hi := (38363681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233171 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233171 / 200000) = 1/(200000 / 233171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10105 : Bounds (153454723 / 1000000000) (38363681 / 250000000) (Real.log (233171 / 200000)) := by
  have h := reflection_log_10105_neg
  have he : Real.log (233171 / 200000) = -Real.log (200000 / 233171) := by
    rw [show ((233171 / 200000) : ℝ) = ((200000 / 233171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10106_neg : (18134803 / 100000000) ≤ -Real.log (166829 / 200000) ∧
    -Real.log (166829 / 200000) ≤ (181348031 / 1000000000) := by
  have h := checkLog_sound (w := (33171 / 366829)) (n := 12)
    (lo := (18134803 / 100000000)) (hi := (181348031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 166829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 166829) = 1/(166829 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10106 : Bounds (-181348031 / 1000000000) (-18134803 / 100000000) (Real.log (166829 / 200000)) := by
  have h := reflection_log_10106_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10107_neg : (27893307 / 1000000000) ≤ -Real.log (38899684759 / 40000000000) ∧
    -Real.log (38899684759 / 40000000000) ≤ (6973327 / 250000000) := by
  have h := checkLog_sound (w := (1100315241 / 78899684759)) (n := 12)
    (lo := (27893307 / 1000000000)) (hi := (6973327 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38899684759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38899684759) = 1/(38899684759 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10107 : Bounds (-6973327 / 250000000) (-27893307 / 1000000000) (Real.log (38899684759 / 40000000000)) := by
  have h := reflection_log_10107_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10108_neg : (13802251 / 500000000) ≤ -Real.log (243193254991 / 250000000000) ∧
    -Real.log (243193254991 / 250000000000) ≤ (27604503 / 1000000000) := by
  have h := checkLog_sound (w := (6806745009 / 493193254991)) (n := 12)
    (lo := (13802251 / 500000000)) (hi := (27604503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243193254991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243193254991) = 1/(243193254991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10108 : Bounds (-27604503 / 1000000000) (-13802251 / 500000000) (Real.log (243193254991 / 250000000000)) := by
  have h := reflection_log_10108_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10109_neg : (333056977 / 1000000000) ≤ -Real.log (62500000000 / 87201674503) ∧
    -Real.log (62500000000 / 87201674503) ≤ (166528489 / 500000000) := by
  have h := checkLog_sound (w := (24701674503 / 149701674503)) (n := 12)
    (lo := (333056977 / 1000000000)) (hi := (166528489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87201674503 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87201674503 / 62500000000) = 1/(62500000000 / 87201674503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10109 : Bounds (333056977 / 1000000000) (166528489 / 500000000) (Real.log (87201674503 / 62500000000)) := by
  have h := reflection_log_10109_neg
  have he : Real.log (87201674503 / 62500000000) = -Real.log (62500000000 / 87201674503) := by
    rw [show ((87201674503 / 62500000000) : ℝ) = ((62500000000 / 87201674503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10110_neg : (167401377 / 500000000) ≤ -Real.log (62500000000 / 87354042163) ∧
    -Real.log (62500000000 / 87354042163) ≤ (66960551 / 200000000) := by
  have h := checkLog_sound (w := (24854042163 / 149854042163)) (n := 12)
    (lo := (167401377 / 500000000)) (hi := (66960551 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87354042163 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87354042163 / 62500000000) = 1/(62500000000 / 87354042163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10110 : Bounds (167401377 / 500000000) (66960551 / 200000000) (Real.log (87354042163 / 62500000000)) := by
  have h := reflection_log_10110_neg
  have he : Real.log (87354042163 / 62500000000) = -Real.log (62500000000 / 87354042163) := by
    rw [show ((87354042163 / 62500000000) : ℝ) = ((62500000000 / 87354042163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10111_neg : (33610983 / 50000000) ≤ -Real.log (125000000000 / 244822485207) ∧
    -Real.log (125000000000 / 244822485207) ≤ (672219661 / 1000000000) := by
  have h := checkLog_sound (w := (119822485207 / 369822485207)) (n := 12)
    (lo := (33610983 / 50000000)) (hi := (672219661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244822485207 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244822485207 / 125000000000) = 1/(125000000000 / 244822485207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10111 : Bounds (33610983 / 50000000) (672219661 / 1000000000) (Real.log (244822485207 / 125000000000)) := by
  have h := reflection_log_10111_neg
  have he : Real.log (244822485207 / 125000000000) = -Real.log (125000000000 / 244822485207) := by
    rw [show ((244822485207 / 125000000000) : ℝ) = ((125000000000 / 244822485207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
